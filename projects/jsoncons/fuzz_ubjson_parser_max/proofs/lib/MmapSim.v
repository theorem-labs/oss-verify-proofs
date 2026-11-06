(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamSim AllocSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__MmapSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim.WithFP1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "2I"]; ["2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3le"; "4firstn"; "4skipn"; "5N"; "5Z"; "6equiv"; "6modeled"; "7omni_strong_equiv"; "8len_word"; "8nat_to_word"]; ["9errno_ret_in"; ":Fs"; ";PhdrInfo"; ";Segment"; ";mkImage"; "<Ok"; "<Unmodeled"; "<outcome"; "=errors"; "=exec"; "=exits_with"; "=omni_run"; ">Build_machine_state"; ">MachineOk"; ">fetch_word"; ">is_ecall"]; [">machine_result"; ">machine_state"; ">ms_gpr"; ">ms_read_bytes"; ">ms_svc_pending"; ">set_gpr0"; ">step"; ">store_ok"; "?SNext"; "?advance_past_svc"; "?apply_effect"; "?config"; "?init_config"; "?init_machine_state"; "?is_prefix"; "?mkCfg"]; ["?mkEntry"; "?obs_trace"; "?reaches_error"; "?run"; "?segments_reserved"; "?sstep"; "?star"; "?step_to"; "?sys_input"; "@syscall_spec"; "AEntryDraw"; "BENOMEM"; "BExitEv"; "BMemCopy"; "BModel"; "BProcInput"]; ["BSyscallEffect"; "BTASK_SIZE"; "Balloc_top"; "Berrno_ret"; "Bevent"; "Bin_arg"; "Bin_argv"; "Bin_envp"; "Bin_fs"; "Bin_hwcap"; "Bin_uid"; "Binit_model"; "Bm_fs"; "Bm_halted"; "Bm_vm_lazy"; "Bm_vmmaps"]; ["Bmap_has"; "BmkEffectU"; "Bpage_round_up_Z"; "Bpage_size"; "Bregion_free"; "Bsource_alloc_limit"; "Btarget_alloc_limit"; "Bvm_backing_used"; "Bvm_limit"; "Bvm_maps"; "Bvm_reserved"; "Cmmap_anon_b"; "Cmmap_errnos"; "Cmmap_modeled_b"; "Cmmap_off_aligned_b"; "Cmmap_spec"]; ["Cmunmap_spec"; "Dw_is0"; "Edecode_any"; "FSZ1"; "FStore"; "Finstr"; "Gbvmap"; "Hreg_get"; "Iwbytes"; "Jbuf_modeled"; "Jbufs_modeled"; "Jfd1chan"; "Jmsteps"; "Jwevents"; "Ltmw"; "Ltmw_post"]; ["Ltwm"; "Ltwm_pend"; "Ltwm_post"; "Ltwm_rest_post"; "Ltwm_tail"; "Ltwo_traces"; "Kgrant_ok"; "Kmmap_args_ok"; "Kmmap_model"; "Kmunmap_args_ok"; "Kmunmap_eff"; "Kmunmap_model"; "Kpage_round_up"; "Ktmw"; "Ktmw_post"; "Ktwo_traces"]; ["Kunfill"; "Kzfill"; "Mfp_csr"; "Mfp_regs"; "Mgetr"; "Mmkst"; "Mrdn"; "Mregupd"; "Mv_addi"; "Mv_srli"; "NIn"; "Oadd"; "Odiv"; "Ole"; "Olt"; "Omodulo"]; ["Oof_nat"; "Opow"; "0a"; "0abrk"; "0addr"; "0alim"; "0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0b"; "0bf"; "0brk0"; "0bs"; "0buf"]; ["0bufs"; "0c"; "0cf"; "0code"; "0code'"; "0cs"; "0e"; "0eff"; "0evs"; "0fs"; "0fx"; "0hint"; "0imm"; "0inp"; "0k"; "0lim"]; ["0lo"; "0m"; "0mb"; "0mem"; "0model"; "0model'"; "0ms"; "0ms'"; "0n"; "0nlen"; "0o"; "0pc"; "0ph"; "0r"; "0rbrk"; "0regs"]; ["0rest"; "0rlim"; "0rmb"; "0rnd"; "0rom"; "0rpc"; "0rph"; "0rrnd"; "0rs1"; "0rs2"; "0rsp"; "0s"; "0segs"; "0sh"; "0source_segs"; "0sp"]; ["0st"; "PBV"; "PZ_to_bv"; "Pbv"; "Pbv_add"; "Pbv_signed"; "Pbv_unsigned"; "0sv"; "0target_segs"; "0tr"; "0tr'"; "0v"; "0w"; "0x"; "0x8"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma v_srli_div : ltac2:(TCodec.tc2 tcn__MmapSim "N'W3yR0%211'J'@&TMzr1%3221&TN+R0%2241%8241'A&W6&TIr3r2%3221%52B1&TL%72D5&U1+2%2217%5241%=3G71p0?1p]LI1p^LK1").
Proof.
intros x sh Hsh. unfold v_srli.
rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.shiftr_div_pow2 by lia.
pose proof (u64_range x) as Hx.
assert (Hp : (0 < 2 ^ sh)%Z) by (apply Z.pow_pos_nonneg; lia).
assert (Hle : (bv_unsigned x / 2 ^ sh <= bv_unsigned x)%Z)
by (apply Z.div_le_upper_bound; nia).
assert (H0 : (0 <= bv_unsigned x / 2 ^ sh)%Z) by (apply Z.div_pos; lia).
apply Z.mod_small. lia.
Qed.
Lemma step_sb_any : ltac2:(TCodec.tc2 tcn__MmapSim "S;'8'Q3%211&SFy5'W3yR0%211%5241';y8%611%311p061yQ0%:11%;1<y<%=11'A%;15&Q>r9r7%3221(2r4%22<1%93841'4&Q?r5%211(6%?3521'='SE'J%3221%N11&SBr6%211(<(SD(SCr3%342@E1+4%64=<21%I2<1%Q03<91&QGr<&TH&TDr;%221@&W5%12Q:Q1%6231u1%:49Q821(>%Q=3Q321'Q@'QA%211&QFr=&TEvUJr:%352DA1QC%6251(Q=%F2DL&SH%G2IQG%E2QNQ@%J221(5&W2&W6%M2OQ;%22R?1%42R<1(:%11R=%83R>31%=3B:1%E5DQ6?1R5%A2J1%R:3JC1p0N1p0Q<1p0QN1p0R51p[JR@1p]DRC1p]BRD1p^JRF1p]:RI1p\8RJ1p\HS11p]0S11p]JS81").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
rewrite <- N_to_le_bytes_1_small.
apply (step_sb segs regs pc mem rom w rs1 rs2 imm); assumption.
Qed.
Lemma step_sb_at : ltac2:(TCodec.tc2 tcn__MmapSim "SC'8'Q3%211&SFy5'W3yR0%211%5241';y8%611%311p061yQ0%:11%;1<y<%=11'A%;15&Q>r<r:%3221(2r7%22<1%93841'4&Q?r8%211(6%?3521'='SE'J%3221%N11&SBr9%211(<(SD(SCr6%342@E1+4%64=<21%I2<1%Q03<91&TH&TDr>%221>&W5%12Q8O%6231%Q83QD1=r?%821D%Q;3QG1@&W2&W6%12QKQ7%32QH1%Q@3QH1E&QGrBu1%342;N1(>%QF3Q<21'Q@'QA%211&QFrC&TEvUJrAr@%453>21G%7261(Q=%Q225Q6&SH(5(:%11R?%33R@QL1%53:R51%>5=H71Q1%92C1%R<3C;1p0G1p0N1p0Q41p0Q81p0QA1p0R31p0R:1pZHRL1p^HS11pZ6S21p[JRH1p]DRK1p]BRL1p^JRN1p]:S11p\8S21p\HS91p]0S91p]JS@1").
Proof.
intros segs regs pc mem rom w rs1 rs2 imm a v b Hf He Hd Ha Hv Hb Hok.
rewrite (step_sb_any segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
- rewrite Ha, Hv, Hb. reflexivity.
- rewrite Ha. exact Hok.
Qed.
Lemma wbytes_snoc : ltac2:(TCodec.tc2 tcn__MmapSim "Q4'8'W3y8%211%411yR0%511';%115p031'A&SHr3r2&3r4(5r1(:%11@%43A31%73B61%;3:91%<3;:8&W4&O&7%12H<%311%53H@1%C371:%E3F91pZHM1pZ6K1p\4I1pZNO1").
Proof.
induction bs as [|x bs IH]; intros m a b.
- cbn [app wbytes length]. rewrite word_add_0. reflexivity.
- cbn [app wbytes length].
rewrite IH. f_equal.
rewrite word1_nat, nat_to_word_add_merge. reflexivity.
Qed.
Definition zfill (a n : word) (m : word -> option byte) : word -> option byte :=
zmem m a n.
Lemma zfill_out : ltac2:(TCodec.tc2 tcn__MmapSim "Q3'W3yR0%211';y8%511%311p051'E&TN&W6r1%22;1r4%42=1%6231&TM&TKr3%92B1%3261%5219%>271'A&TAr5r2%342>91%:12%63G21p081p^LM1p\4I1p\BO1pZ6Q01").
Proof. intros a n m x Hx. exact (zmem_out m a n x Hx). Qed.
Lemma rdn_zfill_out : ltac2:(TCodec.tc2 tcn__MmapSim "QK'8'Q3%211'W3yR0%211';y8%511%311p051'9&TM&TK&W6r2%22<1&U0r1%211%7241&U1+2+R0%3221%=251'Er3%>2H1%<1>%A221r6%B2L1%E231r5%E2O1%G241%I219%<251'A%Q81Q0%Q311&TFr8&TAr7%231?<r4%64521E%746?2F%;3921p0=1p0K1p[NQ:1p^LQA1p\4Q=1p\BQC1pZ6QD1p]JQH1").
Proof.
intros segs a n m x k Hnw Hd. exact (rdn_zmem_out segs m a n x k Hnw Hd).
Qed.
Definition munmap_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n
(mkVmMapsFull (vm_reserved (m_vmmaps m))
(map_remove (vm_maps (m_vmmaps m)) addr)
(maps_subtract (vm_noaccess (m_vmmaps m))
(bv_unsigned addr)
(bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Definition mmap_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
(vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m))
(vm_brk (m_vmmaps m))
(vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m))
(vm_init_sp (m_vmmaps m))) m.
Definition page_round_up (len : word) : word :=
Z_to_bv 64 (page_round_up_Z (bv_unsigned len)).
Definition grant_ok (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n)
&& (vm_backing_used m + n <=? vm_limit (m_vmmaps m))%Z.
Lemma munmap_model_halted : ltac2:(TCodec.tc2 tcn__MmapSim "C'W3yR0%211'R>'A';%114&RM&T;r3r2r1%43321%611%713%;3921p\4=1p\B?1pZ:@1").
Proof. reflexivity. Qed.
Lemma munmap_model_fs : ltac2:(TCodec.tc2 tcn__MmapSim "B'W3yR0%211'R>'A&Q1&RL&T;r3r2r1%43321%611%713%:3921p\4<1p\B>1pZ:?1").
Proof. reflexivity. Qed.
Lemma munmap_model_fd1chan : ltac2:(TCodec.tc2 tcn__MmapSim "A'W3yR0%211'R>&SKr1%211&T;r4r3r2%43321%811p071p\4;1p\B=1pZ:>1").
Proof. intros addr n m H. exact H. Qed.
Lemma munmap_model_no_lazy : ltac2:(TCodec.tc2 tcn__MmapSim "J'W3yR0%211'R>'A'8'=%1255%311&RNr1%211(:%116%:3631&T;r4r3r2%43321%;11%A3=18p081p\4D1p\BF1pZ:G1").
Proof.
intros addr n m Hlazy. unfold munmap_model, with_mmap_destroyed,
vm_forget_range, with_vm_backing, with_vmmaps.
cbn [m_vm_lazy]. rewrite Hlazy. reflexivity.
Qed.
Lemma mmap_model_halted : ltac2:(TCodec.tc2 tcn__MmapSim "C'W3yR0%211'R>'A';%114&RM&T8r3r2r1%43321%611%713%;3921p\4=1p\B?1pZ6@1").
Proof. reflexivity. Qed.
Lemma mmap_model_fs : ltac2:(TCodec.tc2 tcn__MmapSim "B'W3yR0%211'R>'A&Q1&RL&T8r3r2r1%43321%611%713%:3921p\4<1p\B>1pZ6?1").
Proof. reflexivity. Qed.
Lemma mmap_model_fd1chan : ltac2:(TCodec.tc2 tcn__MmapSim "A'W3yR0%211'R>&SKr1%211&T8r4r3r2%43321%811p071p\4;1p\B=1pZ6>1").
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_lazy : ltac2:(TCodec.tc2 tcn__MmapSim "E'W3yR0%211'R>'A'8'=%1255%311&RN&T8r3r2r1%43321%611%713%=3921p\4?1p\BA1pZ6B1").
Proof. reflexivity. Qed.
Lemma grant_ok_unpack : ltac2:(TCodec.tc2 tcn__MmapSim "QM'W3yR0%211'R>'J'A'4&T6r4r3r2r1%544321(>%93821'@&TO&W6%12A9&S3%4221z%A3B21&TN%1236&TM&TK%129A&RB&RO%11F%311%7251&S4&3'=%12Q2Q2&S:%118&S9%11:%73531&W2%12Q:Q1%;33Q31%Q83Q71Q0&S7%11Q7%F21Q6&S8%11D%J231%Q5271%Q62E1%Q72N1%Q82Q11p0Q:1p\BQE1pZ6QH1p\4QH1p[HQJ1").
Proof.
intros hint m a n H. unfold grant_ok in H.
rewrite !andb_true_iff in H.
destruct H as [[[[H1 H2] H3] H4] H5].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
apply Z.leb_le in H5.
auto 7.
Qed.
Lemma region_free_cons : ltac2:(TCodec.tc2 tcn__MmapSim "Q>'W3yR0%211'8'=%1233%311'A'4&S4(5(<r5r4%34<<21r3%63;21r2r1%:3321(>%>3=21'@'E&TM&TK&W6%12J<%22K;%4221r6%52N1%8231%72Q0E%9231%;218%=241%L3HFD%O3N1B%A231p0C1p\BQ71p\2Q81p\LQ51p]HQ:1pZHQ;1").
Proof.
intros b s r lo n H. cbn [region_free] in H.
apply andb_true_iff in H. destruct H as [H1 H2].
split; [|exact H2].
apply negb_true_iff in H1. unfold iv_overlap in H1.
apply andb_false_iff in H1.
destruct H1 as [H1 | H1]; [right | left]; apply Z.ltb_ge in H1; lia.
Qed.
Lemma source_alloc_limit_val : ltac2:(TCodec.tc2 tcn__MmapSim "5'A'J&S5+`PPPPP0%43321").
Proof. vm_compute. reflexivity. Qed.
Lemma target_alloc_limit_val : ltac2:(TCodec.tc2 tcn__MmapSim "5'A'J&S6+`PPPPPP0%43321").
Proof. vm_compute. reflexivity. Qed.
Lemma in_arg3_sys_input : ltac2:(TCodec.tc2 tcn__MmapSim "F'8'Q3%211'QA'W3yR0%211'A&RE&R8r3r2r1%43321u3%7221&QB%1263%;3<31p^N=1p\>A1p]JC1").
Proof. reflexivity. Qed.
Lemma in_arg4_sys_input : ltac2:(TCodec.tc2 tcn__MmapSim "F'8'Q3%211'QA'W3yR0%211'A&RE&R8r3r2r1%43321u4%7221&QB%1263%;3<31p^N=1p\>A1p]JC1").
Proof. reflexivity. Qed.
Lemma in_arg5_sys_input : ltac2:(TCodec.tc2 tcn__MmapSim "F'8'Q3%211'QA'W3yR0%211'A&RE&R8r3r2r1%43321u5%7221&QB%1263%;3<31p^N=1p\>A1p]JC1").
Proof. reflexivity. Qed.
Definition mmap_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_args_ok_gates : ltac2:(TCodec.tc2 tcn__MmapSim "Q4'QA&T7r1%211'@'A'4&S>&QBr2u5%3221%511(>%93821&S;u3%9281%311%>3=16&SAu1%>2=1%311(6%D3C21&S=u2%D2C1%331<B%I3H1A%K261%L2=1%M2C1p0O1p\>Q31").
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.
Definition munmap_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <= TASK_SIZE)%Z /\
map_has (vm_maps (m_vmmaps model)) (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) = true.
Definition munmap_eff (ms : machine_state) : SyscallEffect :=
mkEffectU (Z_to_bv 64 0) [] [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))] [] [].
Lemma syscall_spec_munmap : ltac2:(TCodec.tc2 tcn__MmapSim "Q9'8'Q3%211'QA'W3yR0%211'R>'Q7'R@%211'A'J&W6r3%22:1+VG%63521&C&R9&R8r6r5r4%43321r2%732<1&S@&QB(1%2281u1%42:1%65319C8%@281p0B1p\FJ1p\:N1p^NQ01p\>Q41p]JQ61").
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma munmap_check_modeled : forall ms model eff,
munmap_args_ok ms model ->
check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
then CheckOk (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms model eff (Hal & Hlen & Hnw & Hhas).
unfold check_munmap.
rewrite (proj2 (Z.eqb_eq _ _) Hal).
unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
cbn [negb orb]. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hnw). cbv beta iota.
unfold page_round_up in Hhas. rewrite Hhas. reflexivity.
Qed.
Lemma munmap_ok : ltac2:(TCodec.tc2 tcn__MmapSim "Q@'8'Q3%211'QA'W3yR0%211'R>'A'J&W6r2%2271+VG%63521&T9r4%2216&R9&R8r6r5%33216r3(Q5'R@&T:%116&T;&QB(1%22:1&T<u1%52=1%311%8351=(:'RD%211%@4?=41%G3CB1p0I1p0M1p\:Q51p^NQ71p\>Q;1p]JQ=1").
Proof.
intros segs ms x8 model Hno Ha.
apply (proj2 (syscall_spec_munmap _ _ _ _ _ Hno)). apply check_munmap_sound_ok.
rewrite (munmap_check_modeled ms model _ Ha).
unfold munmap_eff, w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.
Lemma munmap_ok_inv : ltac2:(TCodec.tc2 tcn__MmapSim "QM'8'Q3%211'QA'W3yR0%211'R>'R@'RD%:11'A'J&W6r5%22:1+VG%63521&T9r7%2216&R9&R8r9r8%33216r6(Q5r4r3%34F@21%:3651'@&T:%11;%H3K91&T;&QB(1%22@1&T<u1%52C1%311%8351I%Q23Q6O1(:%11Q6%Q53Q6D1%A241%B2?1p0D1p0Q01p0Q41p[BQ<1p\<Q@1p[@Q@1p\:QB1p^NQD1p\>QH1p]JQJ1").
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply check_munmap_complete_ok in Hspec.
rewrite (munmap_check_modeled ms model eff Ha) in Hspec.
destruct eff as [r ws zs us cs copyins]; destruct ws as [|? ?];
[destruct zs as [|? ?]|]; try discriminate.
destruct cs as [|? ?]; [destruct copyins as [|? ?]|]; try discriminate.
destruct (w_is0 r
&& listNN_eqb us [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))])
eqn:HC; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in HC as [Hr Hus].
unfold w_is0 in Hr. apply bv_eqb_eq in Hr; subst r.
apply listNN_eqb_eq in Hus; subst us.
unfold munmap_eff. auto.
Qed.
Lemma munmap_no_unmodeled : ltac2:(TCodec.tc2 tcn__MmapSim "Q4'8'Q3%211'QA'W3yR0%211'R>'A'J&W6r2%2271+VG%63521&T9r4%2216&D&R9&R8r6r5%33217r3(Q6'R@%211%93541%;11p0=1p0A1p\:I1p^NK1p\>O1p]JQ11").
Proof.
intros segs ms x8 model Hno Ha Hspec.
apply (proj1 (syscall_spec_munmap _ _ _ _ _ Hno)) in Hspec.
apply (check_munmap_complete_unmodeled _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
rewrite (munmap_check_modeled ms model _ Ha) in Hspec.
destruct (w_is0 (Z_to_bv 64 0)
&& listNN_eqb [] [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]);
discriminate.
Qed.
Lemma syscall_spec_mmap : ltac2:(TCodec.tc2 tcn__MmapSim "QA'8'Q3%211'QA'W3yR0%211'R>'Q7'R@%211'A'J&W6r3%22:1+VN%63521&C&R9&R8r6r5r4%43321r2%732<1&S?&QB(1%2281u1%42:1u2%62<1u3%82>1u4%:2@1u5%<2B1%>9;97531AK@%H2@1p0J1p\FQ21p\:Q61p^NQ81p\>Q<1p]JQ>1").
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input, Hno. reflexivity.
Qed.
Lemma ENOMEM_in_mmap_errnos : ltac2:(TCodec.tc2 tcn__MmapSim "5&TJ'J&R;&S<%43321").
Proof. left. reflexivity. Qed.
Lemma mmap_errno_range : ltac2:(TCodec.tc2 tcn__MmapSim "?'J&TJr1&S<%33421'@&TM+1r2%3221+SoO%5231%7231p091p[>>1").
Proof. intros e HIn. exact (errnos_ok_range mmap_errnos e eq_refl HIn). Qed.
Lemma mmap_fail_ok : ltac2:(TCodec.tc2 tcn__MmapSim "QL'8'Q3%211'QA'W3yR0%211'R>'J'A&W6r3%2271+VN%53621&T7r5%211&TJ&S<%23<91&R9&R8r8r7r6%43321(Q5'R@(S1&RCr4%211(:'=y8%Q011%Q511%42Q01%611%62Q2Q2%811'R=%:11'9%;2Q71%=11%B6?86641'RD%@11%G4F3Q21%N3IQ31p0Q01p0Q41p0Q81p[>Q?1p\:QA1p^NQC1p\>QG1p]JQI1").
Proof.
intros segs ms x8 model e Hno Ha HIn.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.
Lemma grant_not_errno : ltac2:(TCodec.tc2 tcn__MmapSim "N'W3yR0%211'R>'J&TMzr1%3221'A'4&T6r5r4r3r2%544321(>%93821&Q0&S<%2218(6%>3=21p061p0A1p\BF1pZ6I1p\:I1p[HK1").
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Lemma mmap_succ_ok : ltac2:(TCodec.tc2 tcn__MmapSim "R='8'Q3%211'QA'W3yR0%211'R>'A'J&W6r3%2271+VN%63521&T7r5%211'4&T6&QBr6(1%3221r4&S2u1%7261%B2G1%411%;476C1(>%H3>21&R9&R8r8r7%3321@(Q5'R@(S1(:'=y8%Q811%Q=11%42Q81%611(5%72Q;Q;(<&T<%Q02@J%211%44Q@Q@N1%>16%83721'R=%A11'9%B2QF1%D11%F6Q6?6741&T8%13Q8;Q@'RD%I11%M4L531%Q33OQD1p0Q51p0QE1p0QI1pZ6R21p\:R21p^NR41p\>R81p]JR:1").
Proof.
intros segs ms x8 model a Hno Ha Hg.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite (grant_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
unfold grant_ok in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[[H1 H2] H3] H4] H5].
rewrite Hflags.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
rewrite H1, H2, H3, H4, H5.
unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
reflexivity.
Qed.
Lemma mmap_ok_inv : ltac2:(TCodec.tc2 tcn__MmapSim "S:'8'Q3%211'QA'W3yR0%211'R>'R@'RD%:11'A'J&W6r5%22:1+VN%63521&T7r7%211&R9&R8r9r8%33216r6(Q5r4r3%34F@21%:3651'@(:%11I%H3I71'E'B&TJr1&S<%33M21(S1&RC%115'=y8%Q;11%Q@11%42Q;1%A11%62Q=Q=%C11'R=%E11'9%;2QB1%H11%@6>86641%Q@3QCQ81%QA3QEQ2Q4%M221%N2E1q[>QC1%K2QD1'4&T6&QBr:(1%3221&S2u1%6251%QM2R51%411%:46QDQ51(>%R33=21(5(<&T<%119%34R=R=Q<1%53Q11Q0%Q;6Q>Q31Q1OL%R;3R>R31&T8%13QA6R0%R>3RBQO1%QJ241%QK2=1qZ6RF1%QH2RG1%QJ2N1%QO2QL1p0R11p0R=1p0RA1p[BRI1p\<RM1p[@RM1p\:RO1p^NS11p\>S51p]JS71").
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hflags in Hspec.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false)
by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
rewrite Hnr in Hspec.
destruct eff as [r ws zs us cs copyins].
cbv beta iota zeta in Hspec.
destruct ws as [|w ws]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Herr; rewrite ?Herr in Hspec;
cbv beta iota in Hspec.
- destruct zs as [|z zs]; [|discriminate].
inversion Hspec; subst.
split; [reflexivity|]. left.
apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
exists e. auto.
- destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
&& region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))
&& (vm_backing_used model
+ page_round_up_Z (bv_unsigned (ms_gpr ms 1))
<=? vm_limit (m_vmmaps model))%Z) eqn:Hcond;
rewrite ?Hcond in Hspec.
2:{ rewrite andb_false_l in Hspec. discriminate. }
destruct (listNN_eqb zs
[(r, Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))]) eqn:Hzs;
rewrite ?Hzs in Hspec.
2:{ rewrite andb_false_r in Hspec. discriminate. }
cbn [andb] in Hspec.
apply listNN_eqb_eq in Hzs. subst zs.
inversion Hspec; subst.
split; [reflexivity|]. right.
exists r. split; [|split].
+ unfold grant_ok. exact Hcond.
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.
Lemma mmap_no_unmodeled : ltac2:(TCodec.tc2 tcn__MmapSim "Q4'8'Q3%211'QA'W3yR0%211'R>'A'J&W6r2%2271+VN%63521&T7r4%211&D&R9&R8r6r5%33217r3(Q6'R@%211%93541%;11p0=1p0A1p\:I1p^NK1p\>O1p]JQ11").
Proof.
intros segs ms x8 model Hno Ha Hspec.
destruct (mmap_args_ok_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
cbv beta iota zeta in Hspec.
assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
rewrite E in Hspec. cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.
Lemma adv_mmap_grant : ltac2:(TCodec.tc2 tcn__MmapSim "R:&SFy5'W3yR0%211%5241';%113y8%711%411p071'A'QA&QI&QJ(Q<r7&TCvUJ%211r6r5(0%11D&TB%117r4r3%=8<9875321(S1r2(:'='8%11J%32Q01%511(5%62Q3Q3(<r1%24Q6Q6;1%;14%63521'R=%>11'9%?2Q<1%A11%D6C=6741%Q42F1%Q611&TE&TG(W1+:(?%33QI21%53Q:1L&TH+4%22Q91&TA%13Q1GQ5%<5Q>631Q5%QF3QE>1p\BQO1pZ6R01p]:QJ1p\8QK1p^@R01p\HR41p]0R41").
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies
apply_writes apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.
Definition unfill (a n : word) (m : word -> option byte) : word -> option byte :=
fun x => if Z.leb (bv_unsigned a) (bv_unsigned x)
&& Z.ltb (bv_unsigned x) (bv_unsigned a + bv_unsigned n)
then None else m x.
Lemma unfill_out : ltac2:(TCodec.tc2 tcn__MmapSim "Q3'W3yR0%211';y8%511%311p051'E&TN&W6r1%22;1r4%42=1%6231&TM&TKr3%92B1%3261%5219%>271'A&T@r5r2%342>91%:12%63G21p081p^LM1p\4I1p\BO1pZ6Q01").
Proof.
intros a n m x Hx. unfold unfill.
destruct Hx as [Hx | Hx].
- rewrite (proj2 (Z.leb_gt (bv_unsigned a) (bv_unsigned x))) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge (bv_unsigned x) (bv_unsigned a + bv_unsigned n))) by lia.
rewrite andb_false_r. reflexivity.
Qed.
Lemma rdn_unfill_out : ltac2:(TCodec.tc2 tcn__MmapSim "QK'8'Q3%211'W3yR0%211';y8%511%311p051'9&TM&TK&W6r2%22<1&U0r1%211%7241&U1+2+R0%3221%=251'Er3%>2H1%<1>%A221r6%B2L1%E231r5%E2O1%G241%I219%<251'A%Q81Q0%Q311&TFr8&T@r7%231?<r4%64521E%746?2F%;3921p0=1p0K1p[NQ:1p^LQA1p\4Q=1p\BQC1pZ6QD1p]JQH1").
Proof.
intros segs a n m x k Hnw Hd. apply rdn_ext; [exact Hnw|].
intros y Hy. apply unfill_out. lia.
Qed.
Lemma adv_munmap : ltac2:(TCodec.tc2 tcn__MmapSim "R=&SFy5'W3yR0%211%5241';%113y8%711%411p071'A'QA&QI&QJ(Q<r7&TCvUJ%211r6r5(0%11D&TB%117r4r3%=8<9875321(S1&W2z%22N1(:'='8%11L%32Q21%511%52Q4Q4%711(5(<r2r1%34Q:Q:21%53716'R=%?11'9%@2Q?1%B11%G6D><641%Q72I1%Q911&TE&TG(W1+:(?%33QL21%53Q=1M&TH+4%22Q<1&T@%13GFQ8%<5QA631Q8%QI3QH>1p\BR21pZ6R31p]:QM1p\8QN1p^@R31p\HR71p]0R71").
Proof.
intros regs pc sv mem rom a n.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) []
= unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd.
rewrite b_npc4, Hm. reflexivity.
Qed.
Section WithSegs.
Variable segs : list Segment.
Inductive twm : machine_state -> Model -> list (list byte) -> word -> Prop :=
| twm_exit : forall ms model x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
twm ms model [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twm_write : forall ms model buf bufs code,
(1 <= length buf)%nat ->
twm_pend ms model buf bufs code ->
twm ms model (buf :: bufs) code
| twm_munmap : forall ms model x8 bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
twm (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) bufs code ->
twm ms model bufs code
| twm_step : forall ms ms' model bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm ms' model bufs code ->
twm ms model bufs code
with twm_pend : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmp_write : forall ms model x8 rest bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
twm_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model
(skipn n rest) bufs code) ->
twm_pend ms model rest bufs code
with twm_tail : machine_state -> Model -> list byte -> list (list byte) -> word -> Prop :=
| twmt_done : forall ms model bufs code,
twm ms model bufs code ->
twm_tail ms model [] bufs code
| twmt_more : forall ms model rest bufs code,
(1 <= length rest)%nat ->
twm_pend ms model rest bufs code ->
twm_tail ms model rest bufs code
| twmt_step : forall ms ms' model rest bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
twm_tail ms' model rest bufs code ->
twm_tail ms model rest bufs code.
Scheme twm_min := Minimality for twm Sort Prop
with twm_pend_min := Minimality for twm_pend Sort Prop
with twm_tail_min := Minimality for twm_tail Sort Prop.
Combined Scheme twm_mutind from twm_min, twm_pend_min, twm_tail_min.
Lemma msteps_twm : ltac2:(TCodec.tc2 tcn__MmapSim "L'QA'R>'8'W3y8%211%411%511yR0%611'SLvVLr5r4%43321'T0r3r2%346521r7%541874p031p081p[8>1p[2A1p\:H1p\@J1p\>K1").
Proof.
intros ms ms' model bufs code H; induction H; [auto|].
intro Hw. eapply twm_step; eauto.
Qed.
Lemma msteps_twm_tail : ltac2:(TCodec.tc2 tcn__MmapSim "N'QA'R>'8'W3y8%211%411%511yR0%611'SLvVLr6r5%43321'T4r4r3r2%4576321r8%6519854p031p091p[8?1p[2B1p]2D1p\:J1p\@L1p\>M1").
Proof.
intros ms ms' model rest bufs code H; induction H; [auto|].
intro Hw. eapply twmt_step; eauto.
Qed.
Lemma twm_write_ret : ltac2:(TCodec.tc2 tcn__MmapSim "SG&SFy5'W3yR0%211%5241';y8%611%311p061'R>'8%115%211'A'J&W6&TDr8(W1+A(?%33F21%6251%82F1+R0%<3;21&SGr9+:%;3N19%4231&W2+1%22Q01%E3Q041%O1H&QC(Q<r:&TCvUJ%211(2%K25F%22Q:1(0%11Q<&TB%118r7%=8<9G642Q11+;%Q23QE1Q0%K2?1+<%Q53QH1Q3%N2B1%E3741r5%A2Q@1%Q?3I31'Fu1&7r6%22QK1%5241'9r1%8271r2%82R1Q<%;221'T4&TE&TGr?&N&Gr3%23R:1Q:%42R;1%736QE1&THr>+4%3221r=r<%?5QA7321r;&H%13RF=QF%D5431R2R<p0F1p0J1p\BM1'T0%RB2;R=%QI2S11%QO8=QK<1QFQD:QN(5%13RKREQE%643R<1Q7p081p0Q71p0Q>1p0R91p0RC1p[8S;1p[2S21p[0S41p\:S71p]:S91p\8S:1p\HSA1p]0SA1").
Proof.
intros regs pc mem rom model buf bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twm_write; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Lemma twm_tail_write_rec : ltac2:(TCodec.tc2 tcn__MmapSim "SD&SFy5'W3yR0%211%5241';y8%611%311p061'R>'8%115%211'A'J&W6&TDr8(W1+A(?%33F21%6251%82F1+R0%<3;21&SGr9+:%;3N19%4231&W2+1%22Q01%E3Q041%O1H&QC(Q<r:&TCvUJ%211(2%K25F%22Q:1(0%11Q<&TB%118r7%=8<9G642Q11+;%Q23QE1Q0%K2?1+<%Q53QH1Q3%N2B1%E3741r5%A2Q@1%Q?3I31'Fu1&7r6%22QK1%5241'9r1%8271r2%82R1Q<%;221'T4&TE&TGr?&N&Gr3%23R:1Q:%42R;1%736QE1&THr>+4%3221r=r<%?5QA7321r;&H%13RF=QF%D5431R2R<p0F1p0J1p\BM1%RA2:R<%QH2S01%QN8<QJ;1QEQC9QM%K51R9RCQCQ4p051p0Q41p0Q;1p0R61p0R@1p[8S81p[2RO1p]2S11p\:S41p]:S61p\8S71p\HS>1p]0S>1").
Proof.
intros regs pc mem rom model rest bufs code H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
apply twmt_more; [exact Hnb|].
eapply twmp_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Lemma twm_munmap_rec : ltac2:(TCodec.tc2 tcn__MmapSim "SM&SFy5'W3yR0%211%5241';y8%611%311p061'R>'8%115%211'A'J&W6&TDr9(W1+A(?%33F21%6251%82F1+VG%<3;21&SGr:+:%;3N19%4231r3%C3N21r;+;%A3Q41?%:231%H3Q316&TOr5%I2Q71&S3%4221z%O3N21&D&W2%12Q>4%Q33Q>91%411&TM&TKr7%Q62QD1&S2r6%Q92QG1%311%7251&RA%:221'4&S0&S9&RO%11Q0%311r8&T<%11A%83431(>%QK3;21'T0&TEvUJ&TGr@%231QAO&THr?+4%3221&T@%@1Ar>%33R521r=%>5=:621&T;r<%23R:71%C441QKR1(Q<rA&TC%11E(2%RB24R=%22S11(0%11S3&TB%11L%;8:8K531HC%Q041B?R8p0>1p0Q31p0Q@1p0QL1p0R21p0R:1p0R@1p0RH1p\DS@1pZ6SA1p[8SB1p[2S91p\:S=1p]:S?1p\8S@1p\HSG1p]0SG1").
Proof.
intros regs pc mem rom model bufs code a nlen H17 Ha Hn Hal Hlen Hnw Hhas Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
eapply twm_munmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold munmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn. auto.
- unfold munmap_eff, ms_gpr. cbn [ms_regs].
rewrite E10, E11, Ha, Hn.
rewrite adv_munmap. exact Hcont.
Qed.
Lemma twm_exit_coden : ltac2:(TCodec.tc2 tcn__MmapSim "R4&SFy5'W3yR0%211%5241';y8%611%311p061'R>'A'J&W6&TDr6(W1+A(?%33C21%6251%82C1+RM%<3;21&SGr7+:%;3K19%4231r2%C3K21&TNr3%D2O1+X0%4221'T0(Q<r9&TCvUJ%211r8(2%N26I%22Q:1(0%11Q<&TB%119%=8<98531IQ3r5(:'8%11Q?%311r4%E47621p0G1p0M1p0Q51p[4QJ1p\:QD1p]:QF1p\8QG1p\HQN1p]0QN1").
Proof.
intros regs pc mem rom model c H17 H10 Hc.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
ms_mem := mem; ms_rom := rom |} 0)
(Z_to_bv 64 255) = c).
{ unfold ms_gpr. cbn [ms_regs]. rewrite E10, H10.
apply land_255_small. exact Hc. }
rewrite <- Hg.
eapply twm_exit.
- cbn [ms_svc_pending]. reflexivity.
- left. exact H17.
Qed.
Lemma sstep_munmap_inv : ltac2:(TCodec.tc2 tcn__MmapSim "RD'QA'R>'W3yR0%211'8'RD%211'R7'A';%117&RMr4%211(0%11<%83631'=%12??%?11&RNr5%211(:%116%A3631&QDr7%211(2%12K9%G3E31'J&W6r6%22Q11+VG%M3521&T9r9r8%3221'R5vVL(QOr:%2217%5441D='@%J1Q<%Q:3Q<:1(QH&QI&QJr;&T:%112%4231%611&T;&QB(1%2281&T<u1%52;1%311%8351F%H2:1%B11%QN3QOQ;1%G2E1p0I1p0Q01p0Q51p0Q<1p0QC1p0QM1p^2R71p[BR91p^NR=1p\:RA1p\>RC1").
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Heff & Hm & Hevs);
subst eff model' evs0
end.
match goal with
| Hmat : materialize_model_accesses
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
inversion Hmat; subst
end.
split; reflexivity.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (Heff & Hm & Hevs); subst eff model' evs0;
rewrite (materialize_model_accesses_no_lazy _ _
(munmap_model_no_lazy _ _ _ Hlazy)) in Hmat;
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite munmap_model_halted, Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hm & _);
subst model';
assert (Hhn : m_halted
(munmap_model (ms_gpr ms 0)
(page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (munmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
Definition twm_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o => tr = wevents bufs ++ [ExitEv code fs] /\ exits_with code tr o.
Definition twm_rest_post (rest : list byte) (bufs : list (list byte)) (code : word)
(fs : Fs.Fs) : post :=
fun tr o => tr = map (WriteEv (Z_to_bv 64 1)) rest ++ wevents bufs ++ [ExitEv code fs]
/\ exits_with code tr o.
Lemma twm_exec_mut : ltac2:(TCodec.tc2 tcn__MmapSim "S2'@'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211'Q9vVL(QOr9r8%3221&T2&RL%114%33;A1%:3951p0<1p0@1p0J1p0Q41p0Q71p[8Q>1p[2QA1p\:QH1p\>QJ1'T1%15Q6QAQ@Q?Q>&SI%11QC%Q?1QD%Q;1K%Q?3Q=1Q8%Q41G%QA3Q61Q1%Q01Jr;r:%N221&T3%K13%24Q0OQ51%Q43Q341p081p0:1p0=1p0@1p0B1p0E1p[8R91p[2R<1p]2R>1p\:RD1p\>RF1'T4%15R2R=R<R;R:p019p[8RA1p[2RD1p]2RF1p\:RL1p\>RN1%S0291%S12Q61").
Proof.
apply (twm_mutind
(fun ms model bufs code =>
bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_post bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))
(fun ms model rest bufs code =>
buf_modeled rest -> bufs_modeled bufs ->
m_halted model = None -> m_vm_lazy model = [] -> fd1chan model ->
OmniRun.exec segs (mkCfg ms model) (twm_rest_post rest bufs code (m_fs model)))).
-
intros ms model x8 Hsvc Hx8 Hbm Hh Hlazy Hfd.
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
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold twm_post. cbn beta. rewrite app_nil_r. cbn [wevents app]. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
intros ms model buf bufs code Hnb Hp IH Hbm Hh Hlazy Hfd.
apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq; [exact (IH Hb Hbs Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents]. rewrite <- app_assoc. reflexivity.
-
intros ms model x8 bufs code Hsvc Hno Hargs Hte IH Hbm Hh Hlazy Hfd.
assert (Hh' : m_halted
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite munmap_model_halted; exact Hh).
assert (Hfd' : fd1chan
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))
by (apply munmap_model_fd1chan; exact Hfd).
apply (exec_step_only segs _ _ []
(mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model))).
+ apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
* exact Hh.
* exact Hsvc.
* apply munmap_ok; [exact Hno | exact Hargs].
* exact Hh'.
* apply materialize_model_accesses_no_lazy.
exact (munmap_model_no_lazy _ _ _ Hlazy).
+ intros evs st Hss.
exact (sstep_munmap_inv ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss).
+ eapply exec_conseq;
[exact (IH Hbm Hh' (munmap_model_no_lazy _ _ _ Hlazy) Hfd') |].
intros tr o (Heq & Hx). split; [| exact Hx].
cbn [app]. rewrite Heq, munmap_model_fs. reflexivity.
-
intros ms ms' model bufs code Hsvc Hstep Hte IH Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
-
intros ms model x8 rest bufs code Hsvc Hno Hg Hr Hnb Hcont IH Hbr Hbm Hh Hlazy Hfd.
apply exec_step; [exact Hh | | |].
+ eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn (length rest) rest))).
* exact Hh.
* exact Hsvc.
* apply write1_ok_n; try assumption. apply Nat.le_refl.
* exact Hh.
* apply materialize_model_accesses_no_lazy. exact Hlazy.
+ intros evs Hss.
destruct (sstep_write_inv segs ms model x8 rest evs SError
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & _ & _ & _ & Habs).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_write_inv segs ms model x8 rest evs (SNext c')
Hh Hlazy Hfd Hsvc Hno Hg Hr Hbr Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbr) Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx].
rewrite Heq. rewrite <- (firstn_skipn n rest) at 3.
rewrite map_app, <- !app_assoc. reflexivity.
-
intros ms model bufs code Hte IH Hbr Hbm Hh Hlazy Hfd.
eapply exec_conseq; [exact (IH Hbm Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). split; [| exact Hx]. cbn [map app]. exact Heq.
-
intros ms model rest bufs code Hnb Hp IH Hbr Hbm Hh Hlazy Hfd.
exact (IH Hbr Hbm Hh Hlazy Hfd).
-
intros ms ms' model rest bufs code Hsvc Hstep Ht IH Hbr Hbm Hh Hlazy Hfd.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbr Hbm Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma twm_exec : ltac2:(TCodec.tc2 tcn__MmapSim "QK'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211'Q9vVL(QOr9r8%3221&T2&RL%114%33;A1%:3951p0<1p0@1p0J1p0Q41p0Q71p[8Q>1p[2QA1p\:QH1p\>QJ1").
Proof. intros ms model bufs code Hte. exact (proj1 twm_exec_mut ms model bufs code Hte). Qed.
Lemma twm_star_admits : ltac2:(TCodec.tc2 tcn__MmapSim "R8'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211'B'QK'R6vVL(QOr:r9%3221&3'RD&SMr8%211(5(R<&RL%11:%32C1%H19%63:21%<3;81%C4B>1Q>q[4E1%G2F1p0I1p0M1p0Q71p0QA1p0QD1p[8QK1p[2QN1p\:R51p\>R71").
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd.
destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Lemma twm_star_only : ltac2:(TCodec.tc2 tcn__MmapSim "R;'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211'RD%Q611'QK'R6vVL(QOr;r:%3221%6451Q3Q2&QN&3&SM%116(5(R<r9&RL%11<%4231%J1D%73E21%;3F91%=3GQB1p0?1p[4G1p^DI1p0L1p0Q01p0Q:1p0QD1p0QG1p[8QN1p[2R11p\:R81p\>R:1").
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) Hstar))
as (tr' & o & _ & Heq & _).
rewrite <- Heq. apply is_prefix_app.
Qed.
Inductive tmw : machine_state -> Model -> list (list byte) -> word
-> list (list byte) -> word -> Prop :=
| tmw_mmap : forall ms model x8 bf cf bs cs,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
(forall e, In e mmap_errnos ->
twm (advance_past_svc (set_gpr0 ms (errno_ret e))) model bf cf) ->
(forall a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true ->
twm (advance_past_svc (apply_effect ms (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])))
(mmap_model a (page_round_up (ms_gpr ms 1)) model) bs cs) ->
(exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true) ->
tmw ms model bf cf bs cs
| tmw_step : forall ms ms' model bf cf bs cs,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
tmw ms' model bf cf bs cs ->
tmw ms model bf cf bs cs.
Lemma msteps_tmw : ltac2:(TCodec.tc2 tcn__MmapSim "Q0'QA'R>'8'W3y8%211%411%511yR0%611'SLvVLr7r6%43321'SNr5r4r3r2%56874321r9%761:9654p031p0:1p[<@1pZNC1p[6B1pZJE1p\:L1p\@N1p\>O1").
Proof.
intros ms ms' model bf cf bs cs H; induction H; [auto|].
intro Hw. eapply tmw_step; eauto.
Qed.
Lemma tmw_mmap_rec : ltac2:(TCodec.tc2 tcn__MmapSim "TH&SFy5'W3yR0%211%5241';y8%611%311p061'R>'8%115%211'A'J&W6&TDr9(W1+A(?%33F21%6251%82F1+VN%<3;21&D&SGr:+;%<3O1:%4231&W2z%22Q11%F3Q141%:11r;+<%E3Q81C%=231+3%:2Q91%N3Q931r<+=%L3Q?1J%D231+Q2%A2Q@1%Q53Q@31r=+>%Q33QF1Q1%K231-1%H2QG1%Q<3QG31r>+?%Q:3QM1Q8%Q2231%QA3QL1L&TJr1&S<%33QD21'T0&TEvUJ&TGrA+:%QG3R:1QE&RCr2%211%73641&THr@+4%3221r?%?5>621I%A41Q1Q8Q?p0C1p[>R81'4&T6%QN2B@&S2%R02DQM%R=2RK1%311%645Q;N1(>%RC3921rB%L31IG%E2LC&TA&T<%R;25R8%211%43M1I%Q55Q4761G&T8%13Q04QA%Q9431R7R@p0=1pZ6S<1'B%RE2?Q7%S22S@;%H11%K43QIQC1%S73M1EqZ6SC1%72SD1'SN(Q<&TC%11QE(2%S<2KS7%22SK1(0%11SM&TB%11QL%:8Q18QK531QCQ@%<61R9R@RGRNS7p0>1p0G1p0Q@1p0R91p0R?1p0RG1p0RO1p0S71p0SC1p[<T;1pZNT21p[6T=1pZJT41p\:T81p]:T:1p\8T;1p\HTB1p]0TB1").
Proof.
intros regs pc mem rom model bf cf bs cs H17 H11 H12 H13 H14 H15
Hfail Hsucc Hex.
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
assert (E13 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg)) by (apply bv_eq; reflexivity).
assert (E14 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg)) by (apply bv_eq; reflexivity).
assert (E15 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg)) by (apply bv_eq; reflexivity).
eapply tmw_mmap.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold mmap_args_ok, ms_gpr. cbn [ms_regs].
rewrite E11, E12, E13, E14, E15.
auto.
- intros e HIn. rewrite adv_set. apply Hfail; assumption.
- intros a Hg. rewrite adv_mmap_grant.
unfold ms_gpr in *. cbn [ms_regs] in *. rewrite E11 in *.
apply Hsucc. exact Hg.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11. exact Hex.
Qed.
Lemma sstep_mmap_inv : ltac2:(TCodec.tc2 tcn__MmapSim "T0'QA'R>'W3yR0%211'8'RD%211'R7'A';%117&RMr4%211(0%11<%83631'=%12??%?11&RNr5%211(:%116%A3631&QDr7%211(2%12K9%G3E31'J&W6r6%22Q11+VN%M3521&T7r9%211'R5vVL(QOr:%2216%5441C<'@r8%J1Q<%Q:3Q<21'E'B&TJr1&S<%33H21(QH&QI&QEr<&RC%118%4231%611r;%G221%:11%QL3QMD1%F2=1q[>Q61%C2Q71'4&T6&QB(1%22@1&S2u1%52C1%Q?2R>1%411%946AL1(>%R<3<21&QJ(S1y8%RG11%RE11%R92RG1%R411(5(<&T<%11@%34RMRMQ:1%53R?1R9'R=%R<11'9%RD2S21%R?11%A6QA<6R?41%C2Q<1%Q?11&T8%13QE<Q:%R1231%QD11%S63S7QN1%R02K1qZ6S=1%QM2S>1%QO2Q;1%R42R11p0R61p0R=1p0RA1p0RH1p0RO1p0S91p^2SC1p[BSE1p^NSI1p\:SM1p\>SO1").
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hargs Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (Hevs & Hcase);
subst evs0
end.
split; [reflexivity|].
destruct Hcase as [(e & HIn & -> & ->) | (a & Hg & -> & ->)].
+ left. exists e.
match goal with
| Hmat : materialize_model_accesses model _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat;
inversion Hmat; subst
end.
split; [assumption |].
rewrite apply_effect_no_write. reflexivity.
+ match goal with
| Hmat : materialize_model_accesses (mmap_model a _ model) _ = Some _ |- _ =>
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat;
inversion Hmat; subst
end.
right. exists a. auto.
-
exfalso.
match goal with
| H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3)
as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans (mmap_model_lazy _ _ _) Hlazy)) in Hmat ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(? & ? & ? & Hm) | (? & ? & ? & Hm)]; subst model';
[ rewrite Hh in H6; discriminate
| rewrite mmap_model_halted, Hh in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (mmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hcase);
destruct Hcase as [(e & _ & _ & Hm) | (a & _ & _ & Hm)]; subst model';
[ rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
| assert (Hhn : m_halted
(mmap_model a (page_round_up (ms_gpr ms 1)) model) = None)
by (rewrite mmap_model_halted; exact Hh);
rewrite (m_killed_of_m_halted_none _ Hhn) in H6; discriminate ]
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (mmap_no_unmodeled segs ms x8 model Hno Hargs H3)
end.
Qed.
Definition tmw_post (bf : list (list byte)) (cf : word) (bs : list (list byte)) (cs : word)
(fs : Fs.Fs) : post :=
fun tr o => (tr = wevents bf ++ [ExitEv cf fs] /\ exits_with cf tr o)
\/ (tr = wevents bs ++ [ExitEv cs fs] /\ exits_with cs tr o).
Lemma tmw_exec : ltac2:(TCodec.tc2 tcn__MmapSim "R2'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%117%217'A';%11>&RMr8%211(0%11C%83631'=%12FF%N11&RNr9%211(:%116%A3631&SKr:%211'Q9vVL(QOr<r;%3221&SOr7&RL%115%45<BK31%;3:61p0=1p0A1p0K1p0Q51p0Q71p0Q:1p[<QC1pZNQF1p[6QE1pZJQH1p\:QO1p\>R11").
Proof.
intros ms model bf cf bs cs Hte.
induction Hte as
[ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
| ms ms' model bf cf bs cs Hsvc Hstep Hte IH];
intros Hbf Hbs Hh Hlazy Hfd.
-
apply exec_step; [exact Hh | | |].
+ eexists; eexists.
apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] []) model model []).
* exact Hh.
* exact Hsvc.
* apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
* exact Hh.
* apply materialize_model_accesses_no_lazy. exact Hlazy.
+ intros evs Hss.
destruct (sstep_mmap_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hargs Hss)
as (_ & [(e & _ & Habs) | (a & _ & Habs)]); discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_mmap_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hargs Hss)
as (-> & [(e & He & Hc') | (a & Hg & Hc')]); injection Hc' as ->.
*
eapply exec_conseq; [exact (twm_exec _ _ _ _ (Hfail e He) Hbf Hh Hlazy Hfd) |].
intros tr o (Heq & Hx). left. split; [cbn [app]; exact Heq | exact Hx].
*
set (n := page_round_up (ms_gpr ms 1)) in *.
assert (Hh' : m_halted (mmap_model a n model) = None)
by (rewrite mmap_model_halted; exact Hh).
assert (Hfd' : fd1chan (mmap_model a n model))
by (apply mmap_model_fd1chan; exact Hfd).
eapply exec_conseq;
[exact (twm_exec _ _ _ _ (Hsucc a Hg) Hbs Hh'
(eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') |].
intros tr o (Heq & Hx). right. split; [| exact Hx].
cbn [app]. rewrite Heq, mmap_model_fs. reflexivity.
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbf Hbs Hh Hlazy Hfd) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma tmw_star_admits_fail : ltac2:(TCodec.tc2 tcn__MmapSim "R<'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%117'A';%11=&RMr7%211(0%11B%83631'=%12EE%M11&RNr8%211(:%116%A3631&SKr9%211'B'QK'R6vVL(QOr<r;%3221&3'RD&SMr:%211(5(R<&RL%11:%32C1%H19%63:21%<3;81%C4B>1Q>q[4E1%G2F1p0I1p0M1p0Q71p0QA1p0QD1p[<QM1pZNR01p[6QO1pZJR21p\:R91p\>R;1").
Proof.
intros ms model bf cf bs cs Hte.
induction Hte as
[ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
| ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
- destruct (twm_star_admits _ _ _ _ (Hfail ENOMEM ENOMEM_in_mmap_errnos)
Hbm Hh Hlazy Hfd) as [c Hstar].
rewrite <- apply_effect_no_write in Hstar.
exists c.
replace (wevents bf ++ [ExitEv cf (m_fs model)])
with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_syscall segs ms model x8 (mkEffect (errno_ret ENOMEM) [] [])
model model []).
+ exact Hh.
+ exact Hsvc.
+ apply mmap_fail_ok; [exact Hno | exact Hargs | apply ENOMEM_in_mmap_errnos].
+ exact Hh.
+ apply materialize_model_accesses_no_lazy. exact Hlazy.
- destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
exists c.
replace (wevents bf ++ [ExitEv cf (m_fs model)])
with ([] ++ (wevents bf ++ [ExitEv cf (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma tmw_star_admits_succ : ltac2:(TCodec.tc2 tcn__MmapSim "R;'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%115'A';%11=&RMr7%211(0%11B%83631'=%12EE%M11&RNr8%211(:%116%A3631&SKr9%211'B'QK'R6vVL(QOr<r;%3221&3'RD&SM%11C(5(R<&RL%119%32Q11%G18%63921%;3:81%B4A=1Q=q[4D1%F2E1p0H1p0L1p0Q61p0Q@1p0QC1p[<QL1pZNQO1p[6QN1pZJR11p\:R81p\>R:1").
Proof.
intros ms model bf cf bs cs Hte.
induction Hte as
[ms model x8 bf cf bs cs Hsvc Hno Hargs Hfail Hsucc Hex
| ms ms' model bf cf bs cs Hsvc Hstep Hte IH]; intros Hbm Hh Hlazy Hfd.
- destruct Hex as [a Hg].
set (n := page_round_up (ms_gpr ms 1)) in *.
assert (Hh' : m_halted (mmap_model a n model) = None)
by (rewrite mmap_model_halted; exact Hh).
assert (Hfd' : fd1chan (mmap_model a n model))
by (apply mmap_model_fd1chan; exact Hfd).
destruct (twm_star_admits _ _ _ _ (Hsucc a Hg) Hbm Hh'
(eq_trans (mmap_model_lazy _ _ _) Hlazy) Hfd') as [c Hstar].
rewrite mmap_model_fs in Hstar.
exists c.
replace (wevents bs ++ [ExitEv cs (m_fs model)])
with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_syscall segs ms model x8 (mkEffect a [] [(a, n)])
(mmap_model a n model) (mmap_model a n model) []).
+ exact Hh.
+ exact Hsvc.
+ apply mmap_succ_ok; [exact Hno | exact Hargs | exact Hg].
+ exact Hh'.
+ apply materialize_model_accesses_no_lazy.
exact (eq_trans (mmap_model_lazy _ _ _) Hlazy).
- destruct (IH Hbm Hh Hlazy Hfd) as [c Hstar].
exists c.
replace (wevents bs ++ [ExitEv cs (m_fs model)])
with ([] ++ (wevents bs ++ [ExitEv cs (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Definition two_traces (bf : list (list byte)) (cf : word)
(bs : list (list byte)) (cs : word)
(fs : Fs.Fs) (tr : list event) : Prop :=
is_prefix tr (wevents bf ++ [ExitEv cf fs]) \/
is_prefix tr (wevents bs ++ [ExitEv cs fs]).
Lemma tmw_star_only : ltac2:(TCodec.tc2 tcn__MmapSim "R9'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%117%217'A';%11>&RMr8%211(0%11C%83631'=%12FF%N11&RNr9%211(:%116%A3631&SKr:%211'RD%Q911'QK'R6vVL(QOr>r=%3221%6451Q4Q3&T5r<r;&RL%118%56843A1Q;p071p[4?1p^DA1p0D1p0H1p0Q21p0Q<1p0Q>1p0QA1p[<QJ1pZNQM1p[6QL1pZJQO1p\:R61p\>R81").
Proof.
intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) Hstar))
as (tr' & o & _ & [(Heq & _) | (Heq & _)]); [left | right];
rewrite <- Heq; apply is_prefix_app.
Qed.
Lemma tmw_no_error : ltac2:(TCodec.tc2 tcn__MmapSim "QL'QA'R>'8'W3y8%211%411%511yR0%611'A';%113&RMr5%211(0%118%83631'=%12;;%C11&RNr6%211(:%116%A3631&SKr7%211'SNr9r8r4%46326<E1&SJ%114%219&D&R2vVL(QOr<r;%3221%6251%811p0:1p0<1p0?1p0E1p0I1p0Q31p[<Q=1pZNQ@1p[6Q?1pZJQB1p\:QI1p\>QK1").
Proof.
intros ms model bf cf bs cs Hh Hlazy Hfd Hte Hbf Hbs. apply exec_no_error.
eapply exec_conseq; [exact (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) |].
intros tr o [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma twm_exec_not_errors : ltac2:(TCodec.tc2 tcn__MmapSim "QJ'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211&D'Q9vVL(QOr9r8%3221&Q8%73621%911p0;1p0?1p0I1p0Q31p0Q61p[8Q=1p[2Q@1p\:QG1p\>QI1").
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd Hex.
destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
destruct (exec_sound _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd) _ _ Hm)
as (_ & Hx).
exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.
Lemma twm_exec_code_unique : ltac2:(TCodec.tc2 tcn__MmapSim "QM'QA'R>'8'W3y8%211%411%511yR0%611'T0r4r3r2r1%544321&SJ%115'A';%11;&RMr5%211(0%11@%83631'=%12CC%K11&RNr6%211(:%116%A3631&SKr7%211'Q9vVL(QOr:r9%3221&Q:%11Q0%83731r8%O3Q8Q41p031p[:Q:1p0>1p0B1p0L1p0Q61p0Q91p[8Q@1p[2QC1p\:QJ1p\>QL1").
Proof.
intros ms model bufs code Hte Hbm Hh Hlazy Hfd code' Hex.
destruct (exec_realizes _ _ _ (twm_exec ms model bufs code Hte Hbm Hh Hlazy Hfd))
as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as ->. reflexivity.
Qed.
Lemma tmw_exec_not_errors : ltac2:(TCodec.tc2 tcn__MmapSim "R0'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%117%217'A';%11>&RMr8%211(0%11C%83631'=%12FF%N11&RNr9%211(:%116%A3631&SKr:%211&D'Q9vVL(QOr<r;%3221&Q8%73621%911p0;1p0?1p0I1p0Q31p0Q51p0Q81p[<QA1pZNQD1p[6QC1pZJQF1p\:QM1p\>QO1").
Proof.
intros ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd Hex.
destruct (exec_realizes _ _ _ Hex) as (tr & o & Hm & Herr).
destruct (exec_sound _ _ _ (tmw_exec ms model bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd) _ _ Hm)
as [(_ & Hx) | (_ & Hx)]; exact (exits_with_never_errors _ _ _ Hx Herr).
Qed.
Lemma tmw_exec_not_fail_only : ltac2:(TCodec.tc2 tcn__MmapSim "RE'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%115'A';%11=&RMr7%211(0%11B%83631'=%12EE%M11&RNr8%211(:%116%A3631&SKr9%211&D&QN'RD&3&SM%11F(5(R<&RLr:%211%42Q91%B1:%73;21%;3<91%;1A%92H6%;3?15%?3@31%B3A51%D11'Q9vVL(QOr<r;%3221&T2%D13%23DO1%93841%O11p0<1p0Q21p0Q61p0Q@1p0QJ1p0QM1p[<R61pZNR91p[6R81pZJR;1p\:RB1p\>RD1").
Proof.
intros ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd Hnp Hex.
destruct (tmw_star_admits_succ ms model bf cf bs cs Hte Hbs Hh Hlazy Hfd) as (c & Hstar).
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma tmw_exec_not_succ_only : ltac2:(TCodec.tc2 tcn__MmapSim "RE'QA'R>'8'W3y8%211%411%511yR0%611'SNr6r5r4r3r2r1%76654321&SJ%117'A';%11=&RMr7%211(0%11B%83631'=%12EE%M11&RNr8%211(:%116%A3631&SKr9%211&D&QN'RD&3&SM%117(5(R<&RLr:%211%42C1%B1:%73;21%;3<91%;1Q0%92Q>6%;3?15%?3@31%B3A51%D11'Q9vVL(QOr<r;%3221&T2%D13%23Q5Q>1%93841%O11p0<1p0Q21p0Q61p0Q@1p0QJ1p0QM1p[<R61pZNR91p[6R81pZJR;1p\:RB1p\>RD1").
Proof.
intros ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd Hnp Hex.
destruct (tmw_star_admits_fail ms model bf cf bs cs Hte Hbf Hh Hlazy Hfd) as (c & Hstar).
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ Hex Hstar)) as (tr' & o & _ & Heq & _).
apply Hnp. rewrite <- Heq. apply is_prefix_app.
Qed.
End WithSegs.
Lemma two_traces_prefix_closed : ltac2:(TCodec.tc2 tcn__MmapSim "Q1'8'W3y8%211%411%511yR0%611&Q1'RD%:11&T?r7r6r5r4r3r2%76654321&QN%13;34r9r8%<621;:97p041p071p^F@1p^DA1p[DD1p[<F1pZNI1p[6H1pZJK1").
Proof.
intros bf cf bs cs fs tr tr' [H | H] Hp;
[left | right]; eapply is_prefix_trans; eauto.
Qed.
Lemma mmap_obs_iff_te : ltac2:(TCodec.tc2 tcn__MmapSim "R@'8'Q3%211'I'Q2'W3yR0%211'R:'J'R?y8%711%=11%>11'T=r=&QMr<r;r:r7&RFr5%211&RG%113&RJ%115&RI%117%>9?=<;:7531&RK&R4%11Br9r8r6%66432B1?r4r3r2r1%L7K<54321&SJ%11F%217'RD%Q@11&C&R1rA&QLr@r?r>%495321Q8Q6Q5Q4E%7361?&T?&RH%11I%36IQ8HQ61C%=251p^D?1p0B1p0D1p0G1p[<QL1pZNQF1p[6QN1pZJQH1p[LQM1p\0QO1p]8R11p\6R31pZLR41p^0R51p\JR91p\HR;1p]JR=1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs tr.
unfold init_config in *.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
assert (Hlazy : m_vm_lazy
(init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
pose proof (tmw_star_only segs ms _ bf cf bs cs Hte Hbf Hbs Hh Hlazy Hfd
tr' c Hstar) as H2.
rewrite Hfs in H2.
eapply two_traces_prefix_closed; eauto.
- intros [Hp | Hp].
+ destruct (tmw_star_admits_fail segs ms _ bf cf bs cs Hte Hbf Hh Hlazy Hfd)
as [c Hstar].
rewrite Hfs in Hstar.
exists (wevents bf ++ [ExitEv cf (in_fs inp)]), c. split; assumption.
+ destruct (tmw_star_admits_succ segs ms _ bf cf bs cs Hte Hbs Hh Hlazy Hfd)
as [c Hstar].
rewrite Hfs in Hstar.
exists (wevents bs ++ [ExitEv cs (in_fs inp)]), c. split; assumption.
Qed.
Lemma mmap_no_error_run_te : ltac2:(TCodec.tc2 tcn__MmapSim "R8'8'Q3%211'I'Q2'W3yR0%211'R:'J'R?y8%711%=11%>11'T=r=&QMr<r;r:r7&RFr5%211&RG%113&RJ%115&RI%117%>9?=<;:7531&RK&R4%11Br9r8r6%66432B1?r4r3r2r1%L7K<54321&SJ%11F%217&D&R2r@&QLr?r>%39421Q5Q3Q2Q1BA%6251%811p0:1p0<1p0?1p[<QD1pZNQ>1p[6QF1pZJQ@1p[LQE1p\0QG1p]8QI1p\6QK1pZLQL1p^0QM1p\JR11p\HR31p]JR51").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
unfold init_config.
apply (tmw_no_error segs _ (init_model (segments_reserved segs) brk0 mb sp lim inp) bf cf bs cs);
[reflexivity | reflexivity | reflexivity | exact Hte | exact Hbf | exact Hbs].
Qed.
Lemma mmap_omni_run_te : ltac2:(TCodec.tc2 tcn__MmapSim "R<'8'Q3%211'I'Q2'W3yR0%211'R:'J'R?y8%711%=11%>11'T=r=&QMr<r;r:r7&RFr5%211&RG%113&RJ%115&RI%117%>9?=<;:7531&RK&R4%11Br9r8r6%66432B1?r4r3r2r1%L7K<54321&SJ%11F%217&Q;(Q4r@r?r>%43321(R0%14Q6Q4Q3Q2&T>&RH%11E%35Q5EQ3C1%<57H5G1p0>1p0@1p0C1p[<QH1pZNQB1p[6QJ1pZJQD1p[LQI1p\0QK1p]8QM1p\6QO1pZLR01p^0R11p\JR51p\HR71p]JR91").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bf cf bs cs Hte Hbf Hbs.
cbn [omni_run]. unfold init_config.
exact (tmw_exec segs _ _ bf cf bs cs Hte Hbf Hbs eq_refl eq_refl eq_refl).
Qed.
Lemma mmap_omni_strong_equiv_te : ltac2:(TCodec.tc2 tcn__MmapSim "S1'8'Q3%211'I'Q2'W3yR0%211'R:y8%511%;11%<11'R?'T=rC&QMrBrAr@r=&RFr1%211&RG%113&RJ%115&RI%117%>9?=<;:7531&RK&R4%11Br?r>&S5%66432B1?r5r4r3r2%L7K<54321r<r;r:r7%J16%H17%G18%F19%Q39O87654321%D1Q0r9r8&S6%I6432;1?r6%Q<7Q6721DCB&SJ%11>%214&M(Q4rGrFrE%43321%53QAQ2Q1(R0rD%241QHQFQE%34QDMLK%;56521Q3p0=1p0?1p0B1p0Q31p[LR11p[<R81pZNR41p[6R:1pZJR61pZDR;1pZ>R=1pZ8R>1pZFR?1pZBRC1pZ@RE1p^BRG1p]@RB1p]6RD1p\NRE1p]FRF1p]>RJ1p]<RL1p]NRN1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bf cf bs cs inp
Hsource Htarget Hbf Hbs.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (mmap_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
Hsource Hbf Hbs) |].
intros tr o [(_ & Hx) | (_ & Hx)];
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bf cf bs cs
Hsource Hbf Hbs tr).
rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
Htarget Hbf Hbs tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bf cf bs cs
Htarget Hbf Hbs).
Qed.
Lemma mmap_strong_equiv_te : ltac2:(TCodec.tc2 tcn__MmapSim "S;'8'Q3%211'I'Q2'W3yR0%211'R:'Jy8%611%<11%=11'R?'T=rE&QMrDrCrBr?&RFr1%211&RG%113&RJ%115&RI%117%>9?=<;:7531&RK&R4%11BrAr@r>%66432B1?r5r4r3r2%L7K<54321r=r<r;r8%J16%H17%G18%F19%Q39?87654321%D1@r:r9r7%I6432;1?r6%Q<7F721DCB&SJ%115%214'@&L&R3(Q4rIrHrG%43321(R0rF%241QIQGQF%944QF1Q3%;11&K%;3Q:Q9QH%74Q9Q2Q1Q0%>42I1Q8%4261%B261p0D1p0F1p0I1p0Q:1p[LR81p[<R@1pZNR;1p[6RB1pZJR=1pZ<RB1pZDRD1pZ>RF1pZ8RG1pZFRH1pZBRL1pZ@RN1p^BS01p]4RJ1p]@RL1p]6RN1p\NRO1p]FS01p]>S41p]<S61p]NS81").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bf cf bs cs inp
Hsource Htarget Hbf Hbs.
split.
{ apply no_error_run_modeled.
apply (mmap_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
Hsource Hbf Hbs). }
right. split.
- intro tr. cbn.
rewrite (mmap_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bf cf bs cs
Hsource Hbf Hbs tr).
rewrite (mmap_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
Htarget Hbf Hbs tr).
reflexivity.
- cbn. apply (mmap_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bf cf bs cs
Htarget Hbf Hbs).
Qed.
End WithFP1.
