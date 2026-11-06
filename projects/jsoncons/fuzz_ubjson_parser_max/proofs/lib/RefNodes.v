(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes StoreOk AgentLib AgentNodes SpecConsts.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__RefNodes () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Nat."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Ioctl."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Kernel.Fork."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel.Fork."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.FileSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes.FPX_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes.FPX_1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes.FPX_1.WithSegs.Openat."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes.FPX_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Scfg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Arith.PeanoNat.Nat."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0B"; "0C"; "1None"; "1O"; "1S"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1negb"]; ["1nil"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3mul"; "3sub"; "4le"]; ["4lt"; "5proj1_sig"; "5sig"; "6Forall"; "7Z"; "0K"; "0KA"; "0KB"; "8len_word"; "8word_to_nat"; "9check_syscall"; ":check_ioctl"; ";check_open_result"; "<check_set_tid_address"; "=check_mmap"; "=check_munmap"]; [">check_mprotect"; "?CheckOk"; "?CheckUnmodeled"; "?check_copyins_after"; "?check_result"; "?clear_copyins"; "?errno_ret_in"; "@file_read"; "@fs_lookup"; "@path"; "Afetch_word"; "Ais_ecall"; "Amachine_state"; "Ams_gpr"; "Ams_svc_pending"; "Ams_writable_byte"]; ["Aset_gpr0"; "Astore_ok"; "Badvance_past_svc"; "Bapply_effect"; "Bbrk_refusal_b"; "Bconfig"; "Binjected_family_off"; "BmkCfg"; "Brefusal_b"; "Bsc_alloc"; "Bsys_input"; "CCstrOk"; "CEISDIR"; "CENAMETOOLONG"; "CENOENT"; "CENOMEM"]; ["CFdDir"; "CFdEntry"; "CFdFile"; "CMemCopy"; "CModel"; "CSyscallEffect"; "CTASK_SIZE"; "CVmMaps"; "Caccess_okb"; "Calloc_fd"; "Calloc_top"; "Ccstr_result"; "Cerrno_ret"; "Cevent"; "Cfd_insert"; "Cfd_lookup"]; ["Cfd_remove"; "Civ_subtract"; "Clive_bytes"; "Cm_fds"; "Cm_fs"; "Cm_halted"; "Cm_tid"; "Cm_vm_lazy"; "Cm_vm_materialized"; "Cm_vmmaps"; "Cmap_contains"; "Cmap_has"; "Cmap_remove"; "Cmaps_subtract"; "Cmaps_subtract_all"; "CmkEffectU"]; ["CmkVmMapsFull"; "Cpage_round_up_Z"; "Cpage_size"; "Cread_bytes_map"; "Cread_cstr"; "Cregion_free"; "Creserved_top"; "Csp_window_lo"; "Ctwo_pow_64"; "Cvm_backed_bytes"; "Cvm_backing_used"; "Cvm_brk"; "Cvm_forget_range"; "Cvm_init_sp"; "Cvm_limit"; "Cvm_live_bytes"]; ["Cvm_maps"; "Cvm_mmap_base"; "Cvm_noaccess"; "Cvm_reserved"; "Cvm_start_brk"; "Cwith_fds"; "Cwith_tid"; "Cwith_vmmaps"; "Dopenat_errnos"; "Dopenat_plain_name"; "Dpath_is_dirref"; "EPID_MAX_ENVELOPE"; "Fbrk_grow_ok"; "Fbrk_unmaps"; "Fbrk_zeros"; "Fmmap_errnos"]; ["Gmprotect_budget_ok"; "Gmprotect_errnos"; "Gmprotect_model_next"; "Hcmd32"; "Hfd32"; "Idelivered_writes"; "Jdot_path"; "Kbv_eqb"; "Kbvmap"; "0N"; "0P"; "Lepend"; "Mbrk_model"; "Mbrk_resolution_ok"; "Nwbytes"; "Ocheck_open_result_copyins"]; ["Omrb"; "Pgrant_ok"; "Pmmap_model"; "Pmunmap_model"; "Punfill"; "Pzfill"; "Qgetr"; "Qmkst"; "Qrdn"; "Qregupd"; "Qseg_rom"; "Qv_addi"; "Upath_at"; "TT1"; "TT2"; "TT3"]; ["Tbrk_adm"; "Tfixed_destroyed_model"; "Tfixed_noaccess_model"; "Tgrant_ok_na"; "Tmmap_fixed_args_ok"; "Tmmap_noaccess_args_ok"; "Tmprotect_model"; "Tnoaccess_model"; "Tthree"; "Ttid_I"; "St_alt3"; "Vcand"; "Vzconflict"; "Vzconflictb"; "Rgrant_ok_na"; "Wfam_on"]; ["XTSet"; "Xnode_ok"; "Xt_alt2"; "Xt_eq"; "Xt_exit"; "Ysrealizes"; "Zmin"; "[In"; "[NoDup"; "[filter"; "\add"; "\le"; "\lt"; "\modulo"; "\mul"; "\of_nat"]; ["\pow"; "\sub"; "\to_nat"; "0a"; "0addr"; "0b"; "0base"; "0brk0"; "0bs"; "0buf"; "0c"; "0cnt"; "0code"; "0count"; "0cuts"; "0d"]; ["0data"; "0e"; "0e0"; "0e1"; "0e2"; "0eff"; "0evs"; "0fd"; "0fds"; "0fx"; "0h"; "0hi"; "0hint"; "0i"; "0j"; "0js"]; ["0k"; "0l"; "0l1"; "0l2"; "0len"; "0lim"; "0lo"; "0m"; "0m'"; "0maps"; "0mbase"; "0mem"; "0mk"; "0model"; "0ms"; "0mx"]; ["0n"; "0nx"; "0off"; "0p"; "0pc"; "0post"; "0r"; "0reads"; "0regs"; "0req"; "0reserved"; "0rom"; "0s"; "0scfg"; "0segs"; "0sp"]; ["]BV"; "]Z_to_bv"; "]bv"; "]bv_add"; "]bv_and"; "]bv_unsigned"; "0sz"; "0t"; "0tid"; "0w"; "0wv"; "0x"; "0x8"; "0z"]]).
Section FPX_1. Context {fx : PropExec.FPState}.
Definition t_alt3 (A B C : TSet) : TSet := t_alt2 A (t_alt2 B C).
Lemma t_alt2_idem : ltac2:(TCodec.tc2 tcn__RefNodes "7&V0&V3&V2r1%2211%4212p261").
Proof. intros A tr. unfold t_alt2. tauto. Qed.
Lemma t_alt3_idem : ltac2:(TCodec.tc2 tcn__RefNodes "7&V0&V3&UJr1%23111%4212p261").
Proof. intros A tr. unfold t_alt3, t_alt2. tauto. Qed.
Lemma with_fds_halted' : ltac2:(TCodec.tc2 tcn__RefNodes "F'='C'XByR0%211'RA%5221%711'RD'H'A%117&S5&T5r2r1%3221%511%613%:3821p_@<1p^B>1").
Proof. reflexivity. Qed.
Lemma with_fds_lazy : ltac2:(TCodec.tc2 tcn__RefNodes "F'='C'XByR0%211'RA%5221%711'RD'H%9266%;11&S7&T5r2r1%3221%511%613%:3821p_@<1p^B>1").
Proof. reflexivity. Qed.
Lemma with_tid_halted : ltac2:(TCodec.tc2 tcn__RefNodes "A'XByR0%211'RD'H'A%114&S5&T6r2r1%3221%511%613%:3821p_@<1pa@>1").
Proof. reflexivity. Qed.
Lemma with_tid_lazy : ltac2:(TCodec.tc2 tcn__RefNodes "C'XByR0%211'RD'H'='C%1255%311&S7&T6r2r1%3221%511%613%<3821p_@>1pa@@1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_lazy' : ltac2:(TCodec.tc2 tcn__RefNodes "D'RG'RD'H'='C'XByR0%211%4211%611&S7&T7r2r1%3221%511%613%?3821p_@A1p^FC1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_eta : ltac2:(TCodec.tc2 tcn__RefNodes "9'RD'H&T7&S9r1%211%4212%63713p_@81").
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.
Lemma vmmaps_eta : ltac2:(TCodec.tc2 tcn__RefNodes "G'RG'H(S@&T3r1%211&T0%113&T2%115&T4%117&SK%119&SN%11;&T1%11=&SM%11?%B8?=;97531%D3E1Ap^FF1").
Proof. intros h. destruct h; reflexivity. Qed.
Lemma Z_to_bv_u_eq' : ltac2:(TCodec.tc2 tcn__RefNodes "A'XByR0%211'Q4'Hr1&XEr2%2271%53641&XA%12:4r3%93;21p051paL<1p]8>1").
Proof.
intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma vm_forget_range_id : ltac2:(TCodec.tc2 tcn__RefNodes "Q1'Q4'RD'H'='C'XByR0%211%4211%611&S7r1%211(@%116%=3631%=19&S8r2%211%71=%C3521&SLr5r4r3%43321%I3J12p071p0>1p_@M1p^HO1p_>Q01").
Proof.
intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
rewrite Hl, Hm. cbn [maps_subtract List.filter].
destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.
Lemma vm_forget_range_lazy_nil : ltac2:(TCodec.tc2 tcn__RefNodes "K'Q4'RD'H'='C'XByR0%211%4211%611&S7r1%211(@%116%=3631&SLr4r3r2%43321%;11%D3=18p081p_@G1p^HI1p_>J1").
Proof.
intros lo hi m Hl. unfold vm_forget_range, with_vm_backing. cbn [m_vm_lazy]. rewrite Hl. reflexivity.
Qed.
Lemma vm_forget_range_halted : ltac2:(TCodec.tc2 tcn__RefNodes "D'Q4'RD'H'A'XByR0%211%411&S5&SLr3r2r1%43321%611%713%>3921p_@@1p^HB1p_>C1").
Proof. reflexivity. Qed.
Lemma access_okb_intro_le : ltac2:(TCodec.tc2 tcn__RefNodes "K'XByR0%211'Q4&V;zr1%3221&V:&XEr3%22:1r2%5221&RF%;221'H'9&RHr4%221:(E%63521p081p0A1p`2F1p]<H1").
Proof.
intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma mmap_check : ltac2:(TCodec.tc2 tcn__RefNodes "Q;'QL'XByR0%211'RD'RE'H'Q4&XEr3%2281+VN%63521'QD&Q:&R:vX>r5r4%43321r2%7321<&Q>&QM(4%2281u1%42:1u2%62<1u3%82>1u4%:2@1u5%<2B1%>8;97531@K%O3H@1p0J1p^<Q21p_LQ41paJQ61p_NQ:1").
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
Lemma munmap_check : ltac2:(TCodec.tc2 tcn__RefNodes "Q3'QL'XByR0%211'RD'RE'H'Q4&XEr3%2281+VG%63521'QD&Q:&R:vX>r5r4%43321r2%7321<&Q?&QM(4%2281u1%42:1%64318C%G3@81p0B1p^<J1p_LL1paJN1p_NQ21").
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
Lemma check_syscall_29 : ltac2:(TCodec.tc2 tcn__RefNodes "Q7'QL'XByR0%211'RE'RD'H'Q4&XEr3%2281+M%63521'QD&Q:&R:vX>r5r4%43321r2%732<1&Q;&TD&QM(4%2291%411&TCu1%62=1%311%:451G<%K3D<1p0F1p_@N1p^<Q01paJQ21p_NQ61").
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Lemma check_syscall_226 : ltac2:(TCodec.tc2 tcn__RefNodes "Q5'QL'XByR0%211'RE'RD'H'Q4&XEr3%2281+W2%63521'QD&Q:&R:vX>r5r4%43321r2%732<1&Q@&QM(4%2281u1%42:1u2%62<1%85531E:%I3B:1p0D1p_@L1p^<N1paJQ01p_NQ41").
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Lemma check_syscall_96 : ltac2:(TCodec.tc2 tcn__RefNodes "N'QL'XByR0%211'RE'RD'H'Q4&XEr3%2281+S0%63521'QD&Q:&R:vX>r5r4%43321r2%732<1&Q=%12>3%B3;31p0=1p_@E1p^<G1paJI1p_NM1").
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.
Inductive three : Type := T1 | T2 | T3.
Lemma rz_alt3 : ltac2:(TCodec.tc2 tcn__RefNodes "Q7'R5'UHp012&V0&V1vX>vX=r5(@'RM%211q0:1r4%96876<21'V5(U=%911%34<;15r6(U>%211%74@?19r7(U?%211%;4DC1=r9&UJ%136:E%?4HG31p051p0:1p0?1p0D1p6O1p4Q01p2Q11p`4Q31p]FQ61").
Proof.
intros c nx A B C Hnode HA HB HC.
apply (srz_conseq segs scfg c (t_alt (fun i => match i with T1 => A | T2 => B | T3 => C end))).
- apply (rz_cases segs scfg c three nx _ T1 Hnode). intros [| |]; assumption.
- intros tr. unfold t_alt3, t_alt2, t_alt. split.
+ intros [[| |] H]; tauto.
+ intros [H | [H | H]]; [exists T1 | exists T2 | exists T3]; exact H.
Qed.
Lemma node_of_iff : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
(forall i, sstep_cfg segs scfg c (evs i) (SNext (nx i))) ->
(forall e st, sstep_cfg segs scfg c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
node_ok segs scfg c I evs nx.
Proof. intros; split; assumption. Qed.
Lemma adv_ret_epend : ltac2:(TCodec.tc2 tcn__RefNodes "QK&THy5'XByR0%211%5241'Ay8%611%311p061'H'QL&R2&R3&TKvW9r6r5r4r3r2%76654321(S?r1(@'C'=%11D%32I1%511%52KK%711'RC%911'>%:2Q01%<11%?6>86641%I2A1%K11&U7&U9(X@+:(F%33Q=21%53N1G&U;+4%22Q01%:5Q341Q0O%Q93Q8<1p`>QA1paJQB1p`HQ=1p_HQ>1p`:QE1p`BQE1").
Proof. intros. unfold epend. apply adv_eff_ret. Qed.
Lemma adv_zeros1_epend : ltac2:(TCodec.tc2 tcn__RefNodes "R5&THy5'XByR0%211%5241'Ay8%611%311p061'H'QL&R2&R3&TKvW9r8r7r6r5r4%76654321(S?r3(@'C'=%11D%32I1%511(:%62LL(Br2r1%34Q0Q021%<15%73621'RC%?11'>%@2Q61%B11%E6D>6741%O2G1%Q111&U7&U9(X@+:(F%33QC21%53Q41M&U;+4%22Q61&U5%13HGQ7%<5Q;631Q7%QA3Q@>1p`2QI1p]8QJ1p`>QK1paJQL1p`HQG1p_HQH1p`:QO1p`BQO1").
Proof.
intros. unfold epend.
assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
{ cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.
Lemma adv_unmaps1_epend : ltac2:(TCodec.tc2 tcn__RefNodes "R5&THy5'XByR0%211%5241'Ay8%611%311p061'H'QL&R2&R3&TKvW9r8r7r6r5r4%76654321(S?r3(@'C'=%11D%32I1%511%52KK%711(:(Br2r1%34Q1Q121%53716'RC%?11'>%@2Q61%B11%E6D><641%O2G1%Q111&U7&U9(X@+:(F%33QC21%53Q41M&U;+4%22Q61&U4%13GFQ7%<5Q;631Q7%QA3Q@>1p`2QI1p]8QJ1p`>QK1paJQL1p`HQG1p_HQH1p`:QO1p`BQO1").
Proof.
intros. unfold epend.
assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
{ cbn [apply_writes apply_zeros].
apply functional_extensionality. intro x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity. }
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.
Lemma adv_write1_epend : ltac2:(TCodec.tc2 tcn__RefNodes "R5&THy5'XByR0%211%5241'Ay8%611%311p061'=%114'H'QL&R2&R3&TKvW9r8r7r6r5r4%76654321(S?r3(:'C%12IA(Br2r1%34ME21(@%116%93731%92Q1Q1%411'RC%611'>%>2Q61%911%C6B86641%M2E1%O11&U7&U9(X@+:(F%33QC21%53Q21K&U;+4%22Q41&TN%13Q5KJ%<5Q9631Q5%Q?3Q>>1p^2QA1p]DQJ1p`>QK1paJQL1p`HQG1p_HQH1p`:QO1p`BQO1").
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.
Lemma rz_close : ltac2:(TCodec.tc2 tcn__RefNodes "T0&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'RA&V0'H%;14&QJvX>r7%3221(6r4%22;1%93841'9&QKr5%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r8%211(@%116%O3631&U6r<(X@+A(F%33QD21%6251&XA+QI%22QF1%Q:3QF41r=+:%;3QL19%>231%Q?3QK1D&V<&XEr9%22R01&V@+2+Q0%3221%8251%R31QK&RO&S3%11Kr:%4221%QI2R1=%R03721'V5vX=(R7&U7vW9&U9r@z%Q22RF1%433M1&U;r?+4%3221r>&U:%11R>%>5=8431&T5&S0%J1Q:r;%3221%521Q=%F271%I4RGH1Q8rA%H5G1E@;%J21>%M4RKL1Q1p051p0Q01p0Q91p0QC1p0QI1p0R51p0R@1p0RG1p0RN1pR<S91p^4S;1p^@SF1paDS>1p_LSA1p_HSC1p`:SJ1p`BSJ1").
Proof.
intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
- intros eff. rewrite (check_syscall_57 segs) by (rewrite H17; apply u64_lit; lia).
unfold check_close. rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32), Hlk. reflexivity.
- rewrite with_fds_halted'. exact Hh.
- rewrite with_fds_lazy. exact Hlazy.
Qed.
Lemma rz_ioctl_winsz : forall regs (pc : word) mem model w fd e K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 29 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some e ->
match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end = true ->
getr regs 11 = Z_to_bv 64 0x5413 ->
srealizes segs scfg (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
model) K ->
srealizes segs scfg (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hnd H11 Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros eff. rewrite check_syscall_29 by (rewrite H17; apply u64_lit; lia).
unfold check_ioctl. rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), Hlk, H11.
destruct e; first [reflexivity | discriminate Hnd].
Qed.
Lemma rz_read_dir : ltac2:(TCodec.tc2 tcn__RefNodes "T;&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11&V0'H%:13&QJvX>r6%3221(6r3%22:1%93841'9&QKr4%211(E%?3521%I1K&S5%11>(3%11O%E3531'='C%12Q3Q3%311&S7r7%211(@%116%O3631&U6r;(X@+A(F%33QC21%6251&XA+QO%22QE1%Q:3QE41r<+:%;3QK19%>231%Q?3QJ1D&V<&XEr8%22QO1&V@+2+Q0%3221%8251'RA%R311&RO&S3%11Lr9%4221(R@%QK281%R23831&V;&V:r?+;%Q53RE1Q3%Q8231%H2RE1+<%Q93RI1Q7%Q<271%L2RI1%:251&RF%=221'V5vX=(R7&U7vW9&U9r@&RL&R<%211%534Q>1&U;+4%22I1r>&U:%11RN%>5=7431r=%A221r:%E4S3D21rA%D5C1AQ37%F21:%I4S7H1R9p051p0L1p0Q;1p0QF1p0R01p0R61p0RB1p0RM1p0S41p0S;1pR<SF1p^@T11paDSI1p_LSL1p_HSN1p`:T51p`BT51").
Proof.
intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hts Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (rewrite H17; apply u64_lit; lia).
unfold check_read. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
rewrite (access_okb_intro_le _ _ (proj1 (bv_unsigned_in_range 64 (getr regs 12))) Hts).
reflexivity.
Qed.
Lemma rz_read_dir_cnt : ltac2:(TCodec.tc2 tcn__RefNodes "TB&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r7%3221(6r4%22;1%93841'9&QKr5%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r8%211(@%116%O3631&U6r<(X@+A(F%33QD21%6251&XA+QO%22QF1%Q:3QF41r=+:%;3QL19%>231%Q?3QK1D&V<&XEr9%22R01&V@+2+Q0%3221%8251'RA%R411&RO&S3%11Lr:%4221(R@%QK281%R23831r@+<%Q33RD1Q1%Q6231%Q02RD9%R83RD21&V;zr;%3221&V:rB+;%Q>3RO1Q<%QA231%Q12RO1%621QB&RF%<221'V5vX=(R7&U7vW9&U9rC&RL&R<%211%534QC1&U;+4%22E1rA&U:%11S3%>5=7431%@21Q5%C4S6B1R8rD%B5A1?M5%D218%G4S:F1R2p051p0J1p0Q41p0Q91p0Q@1p0QK1p0R51p0R;1p0RG1p0S21p0S91p0S@1pR<SK1p]HSM1p^@T81paDT01p_LT31p_HT51p`:T<1p`BT<1").
Proof.
intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc0 Hts Hc.
eapply (rz_read_dir regs pc mem model w fd K); try eassumption.
rewrite H12, u64_lit; [exact Hts|]. unfold TASK_SIZE in Hts. pose proof (u64_range (getr regs 11)). lia.
Qed.
Lemma read_file_check : ltac2:(TCodec.tc2 tcn__RefNodes "U<'QL'XByR0%211'RD&QI'=y8%711%311'H'Q4&XEr7%22<1+QO%63521&QMr9(4%3221r6%<3C21&V<&V@+2+Q0%3221%52>1'A'RA%211&RO&S3%11@r8%4221(6(RB%12JB%32:1%O3:51%=1Q1&QH&S4r:%211%421<%;2Q7K%Q73721&SC&QOvX>r=%3221u1%Q7231u2%Q9251%93531%QB3B1<zr>%Q>216%QD2QN1%Q:241&V;r?%QC21;%QI2R31+RPP0%5221'9&RHr@%QJ21D%QK22C%R12R;1%5231(E%R63821&QGr;r<rA%R421L%53431&T5&RN%QH1?&XC&Q8r1%22RE1%43RLQ91%QI2Q11%837M1%:21G'G'RE'RM%RO11&J'QD&Q:&R:rFrE%33QH21r3rD%73321(QAr2%221F%S93<41(S?r5%K2S>1&TE%S72>R1%2214(@'C%12SISI%311'RC%511'>%62SN1%811%?6=:6641%SJ3Q1G1r4%SL3T2E1%=1Q3%SN3Q3Q<1%Q7231%Q8261%Q52H1p^>Q71p`0T91p^<Q;1&KrC%Q83RMQ31rB%Q;32QG1(QB%T;3Q>21%711p^<QD1%QF2:1t_BTEQH1t]BTAR41p0R;1p0RE1p0RL1p0S21p0S>1p0SG1p0T51p0T<1p0TC1paFTK1p^2TL1p`6U31p`8U21p^@U51p_LU51paJU71p_NU;1").
Proof.
intros ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs Hw Hpos Hcnt65 Haok bs m'.
assert (Hcnt : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z) by (pose proof rw_bytes_max_ge17; lia).
assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
<= bv_unsigned (ms_gpr ms 2))%Z).
{ unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (u64_range (ms_gpr ms 2)) as Hc.
rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
rewrite Z.mod_small; lia. }
assert (Hred : forall eff, check_syscall (sys_input segs ms x8) eff model =
match bs, eff with
| [], _ => check_ret_only eff (Z_to_bv 64 0) m' []
| _ :: _, mkEffectU ret [(a, bs')] [] [] [] [] =>
if bv_eqb a (ms_gpr ms 1) && listN_eqb bs' bs && bv_eqb ret (len_word bs)
then CheckOk m' [] else CheckReject
| _ :: _, _ => CheckReject
end).
{ intros eff. rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
rewrite H0, (fd32_id fd Hfd32), Hlk. cbv beta iota.
rewrite Haok. cbn [negb]. cbv beta iota.
rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
rewrite Hfs. cbv beta iota zeta. rewrite in_wmem_si.
rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
fold bs. fold m'.
destruct bs as [|b bsr]; reflexivity. }
split.
- intros eff mx evs. rewrite Hred. destruct bs as [|b bsr].
+ rewrite check_ret_only_ok_iff. cbn [delivered_writes]. unfold len_word. cbn [length Z.of_nat]. tauto.
+ destruct eff as [ret ws zs us cs ci]. split.
* intro H.
destruct ws as [|[a bs'] [|? ?]]; try discriminate.
destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))%bool eqn:E;
[|discriminate].
apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3. subst.
injection H; intros; subst. repeat split; reflexivity.
* intros (E1 & -> & ->). cbn [delivered_writes] in E1. injection E1; intros; subst.
rewrite !bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl). reflexivity.
- intros eff. rewrite Hred. destruct bs as [|b bsr].
+ apply check_ret_only_no_unmodeled.
+ destruct eff as [ret ws zs us cs ci].
destruct ws as [|[a bs'] [|? ?]]; try discriminate.
destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (_ && _)%bool; discriminate.
Qed.
Lemma rz_read_file : ltac2:(TCodec.tc2 tcn__RefNodes "V3&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11&QI'=%118'Q4&V0'H%>17&QJvX>r:%3221(6r7%22>1%93841'9&QKr8%211(E%?3521%M1O&S5%11>(3%11Q3%E3531'C%12Q6Q6%L11&S7r;%211(@%116%N3631&U6r?(X@+A(F%33QF21%6251&XA+QO%22QH1%Q93QH41r@+:%;3QN19%>231%Q>3QM1D&V<&XEr<%22R21&V@+2+Q0%3221%8251'RA%R611&RO&S3%11Lr=%4221(RB%12?Q6%QK291%R23941%R@1R6&QH&S4%11L%321:%R22R;Q>%R93621rD+<%Q;3RN1Q9%Q>231%Q82RNQD%R?3RN21&V;+1%221Q1+RPP0%42G1r>+R0%Q42Q31%Q9231&R1rFrH+;%QL3S?1QJ%QO231&VB%11R0%84RN731%S23RH1RD&V:rI%R6218%QF2SF1%421QM&RF%I221&QGrBrCrJ%R?21Q2%53431'V5vX=(R7&U7vW9&U9rK&Q8r1%22T41%534R>1&U;+4%22@1&TN%S029Q2%23L18&U:%11SO%@5?9631&T5&RN%R;1Q;rE&XC%13TIQO@%R;231%635QA1%821QA%K2:1rA%O4T<N21rL%N5M1KQ4?%Q021Q>%Q34T@Q21Q8p051t]BTHQ61p0Q=1p0QE1p0R01p0R51p0R81p0R<1p0RC1p0RK1p0S71p0SA1p0SG1p0T31p0T=1p0TD1p0TK1pR<U61p]HU81p^2U:1p`6UG1p`8U>1p^@UI1paDUA1p_LUD1p_HUF1p`:UM1p`BUM1").
Proof.
intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hok Hts bs Hc.
assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
{ unfold ms. rewrite ms_gpr_epend2, H12. apply u64_lit. lia. }
destruct (read_file_check ms (getr regs 17) model fd p off data wv Hno
ltac:(unfold ms; rewrite ms_gpr_epend0; exact Hfd) Hfd32 Hlk Hfs
ltac:(unfold ms; rewrite ms_writable_byte_epend, ms_gpr_epend1, ms_gpr_epend2, H12; exact Hw)
ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_epend1; apply access_okb_intro_le; lia)) as [Hchk Hnu].
unfold ms in Hchk, Hnu. rewrite ms_gpr_epend1, ms_gpr_epend2 in Hchk.
subst bs. revert Hc Hchk.
generalize (file_read data off (getr regs 12)) as bs. intros bs Hc Hchk.
eapply (rz_det segs scfg _ model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
[exact Hh | reflexivity | exact Hchk | exact Hnu
| rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
destruct bs as [|b bsr]; cbn [delivered_writes].
- unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
- unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.
Lemma check_copyins_after_open_result : ltac2:(TCodec.tc2 tcn__RefNodes "N'='C'XByR0%211'>%5221%711'RE'RDp061'H'QD&QCr4r3&Q<&QE%113r2r1%53321%93871&TO%14:954%>3=31p_J@1p_@B1p^<D1p`@F1").
Proof.
intros reads eff m mk. unfold Prelude.check_copyins_after, check_open_result_copyins.
destruct (check_open_result (clear_copyins eff) m mk) eqn:E; [reflexivity|reflexivity|].
exfalso. exact (check_open_result_never_unmodeled _ _ _ E).
Qed.
Section Openat.
Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
Variable w : bv 32.
Hypothesis HF : fetch_word segs pc = Some w.
Hypothesis HE : is_ecall w = true.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
Hypothesis H10 : getr regs 10 = AT_FDCWD.
Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.
Hypothesis Hfs_on : sc_fs scfg = true.
Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
Let fds := m_fds model.
Lemma Hno56 : ltac2:(TCodec.tc2 tcn__RefNodes "?'H'Q4&XEyR0&U6vX8(X@y5+A(F%43321%7261%:291+QH%>3=21").
Proof. rewrite H17. apply u64_lit. lia. Qed.
Lemma fam_on_openat_ms : ltac2:(TCodec.tc2 tcn__RefNodes "5&UOvX>vX=vWN%43321").
Proof. apply (fam_on_openat segs scfg ms (getr regs 17)); [reflexivity | exact Hno56 | exact Hfs_on]. Qed.
Lemma openat_check_head : forall eff,
check_syscall (sys_input segs ms (getr regs 17)) eff model
= Prelude.check_copyins_after (open_copyins ms) eff
match read_cstr (mrb segs mem) (getr regs 11) with
| CstrTooLong => check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG) model []
| CstrFault => check_ret_only (clear_copyins eff) (errno_ret EFAULT) model []
| CstrOk p =>
if path_eqb p [] then check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
else if path_has_slash p then Open.check_openat_sep p (getr regs 12) (clear_copyins eff) model
else if path_is_dirref p then
check_open_result (clear_copyins eff) model (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model)
else match fs_lookup (m_fs model) p with
| None => check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []
| Some _ => check_open_result (clear_copyins eff) model
(fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model)
end
end.
Proof.
intros eff. cbv delta [ms].
rewrite (check_syscall_56 segs _ _ eff model Hno56). unfold check_openat.
rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2.
rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota zeta.
unfold Open.check_openat_body. rewrite in_mem_si, ms_read_byte_epend.
unfold open_copyins. rewrite ms_read_byte_epend, ms_gpr_epend1.
destruct (read_cstr (mrb segs mem) (getr regs 11)) as [p| |]; [|reflexivity|reflexivity].
destruct (path_eqb p []); [reflexivity|].
rewrite H10. norm_fd32. rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
unfold Open.check_openat_resolved.
destruct (path_has_slash p); [reflexivity|].
rewrite Hfl. cbn [Z.eqb]. reflexivity.
Qed.
Lemma rz_openat_toolong : ltac2:(TCodec.tc2 tcn__RefNodes "QK'='XBy8%211%411&V0'H'A%114&U8vX>vWK&U6vX8(X@y5+;(F%43321%7261uTP0%<4;:21(6r2%22D1%C3A41&K&V7&XAz%22L1r3%53M21%711'V5vX=(R7vX5&RL&R=%211%411vWM%7221%:4Q291=&U7vW9vX4&U:%11Q7%554Q53Q71%?219r4%C4Q;B21p0:1p0F1p0O1pR<QD1p]BQF1").
Proof.
intros bs K Hrd Hnz Hc. cbv delta [post] in *.
pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite openat_check_head, Hp. apply check_copyins_after_ret_only.
Qed.
Definition path_at (p : list byte) : Prop :=
(length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
/\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).
Lemma path_at_cstr : ltac2:(TCodec.tc2 tcn__RefNodes "N'='XBy8%211%411&U<r1%211'H'RK&SD&U0vX>vWK%3221&U6vX8(X@y5+;(F%43321%7261%=291(R;r2%211%C3B41p0E1p`8I1").
Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.
Lemma rz_openat_empty : ltac2:(TCodec.tc2 tcn__RefNodes "Q3&V0&U<(@'XBy8%211%411%611'V5vX>vX=(R7vX5&RL&R>%211%411vWM%7221r2%<4;:21&U7vW9vX8vX4vWK&U:%11B%7565431%B21<r3%G4FE21p0<1p0J1pR<Q21").
Proof.
intros K Hp Hc. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite openat_check_head, (path_at_cstr [] Hp). apply check_copyins_after_ret_only.
Qed.
Lemma rz_openat_absent : ltac2:(TCodec.tc2 tcn__RefNodes "QN'='XBy8%211%411&V0&U<r2%211&K'Hr3(@%11:%43:31%611'9&T9r4%211(E%;3521'A%11C&QH&S4vWM%211r5%5221(3%11K%F3931'V5vX>vX=(R7vX5&RL&R>%211%411%621@%:4981?&U7vW9vX8vX4vWK&U:%11@%7565431%@21Jr6%E4DC21p0<1p0H1p0Q41p0Q;1p0QC1pR<QG1p`8QI1").
Proof.
intros p K Hp Hne Hpl Hfs Hc. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
apply check_copyins_after_ret_only.
Qed.
Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.
Lemma rz_openat_dirref : ltac2:(TCodec.tc2 tcn__RefNodes "R3'='XBy8%211%411&V0&U<r3%211'H'9&T:r4%211(E%63521'Q4&V7r1&T8%33421'V5vX>vX=(R7vX5&RLr2%211%411vWM%7221r6%<4;:21p0>1p^4C1&RIvW8%211%>11&T5&RN(R@%23651%421>%E261%I4HG1Q2&U7vW9vX8vX4vWK&U:%11O%7565431%O21I&V2r5%22J1%Q64Q5Q441p0>1p0J1p0Q?1p0QG1pR@QK1pR>QL1p`8QN1").
Proof.
intros p KA KB Hp Hdr HA HB. cbv delta [post] in *.
assert (Hne : p <> []) by (intros ->; discriminate Hdr).
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | exact fam_on_openat_ms | |].
- intros eff. fold ms. rewrite openat_check_head, (path_at_cstr _ Hp).
rewrite (path_eqb_neq _ _ Hne), (path_is_dirref_no_slash _ Hdr), Hdr.
apply check_copyins_after_open_result.
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.
Lemma rz_openat_dot : ltac2:(TCodec.tc2 tcn__RefNodes "QF&V0&U<&TF%211'Q4&V7r1&T8%33421'V5vX>vX=(R7vX5&RLr2%211%411vWM%7221r5%<4;:21p0>1p^4C1&RIvW8%211%>11&T5&RN(R@%23651%421>%E261r3%J4IH21&U7vW9vX8vX4vWK&U:%11Q0%7565431%Q021J&V2r4%22K1%Q74Q6Q541p0>1p0K1p0Q@1pR@QD1pR>QE1").
Proof. intros KA KB Hp. apply (rz_openat_dirref dot_path KA KB Hp). reflexivity. Qed.
Lemma rz_openat_file : ltac2:(TCodec.tc2 tcn__RefNodes "RK'='XBy8%211%411&V0&U<r4%211&K'Hr5(@%11:%43:31%611'9&T9r6%211(E%;3521'A%11C&QH&S4vWM%211r7%5221(6%12K=%F3931'Q4&V7r1&T8%33421'V5vX>vX=(R7vX5&RLr2%211%411%621Er8%;4:921p0=1p^4B1&RIvW8%211%=11&T5&RN(RBr9&XAyR0z%3221%6251%83<;1%:21Q8%J2<1%N4ML1QB&U7vW9vX8vX4vWK&U:%11Q4%7565431%Q421QC&V2%12OQC%Q:4Q9Q831p0=1p0O1p0QC1p0QO1p0R61p0R>1pR@RB1pR>RC1p^0RE1p`8RF1").
Proof.
intros p d KA KB Hp Hne Hpl Hfs HA HB. cbv delta [post] in *.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_open; [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | exact fam_on_openat_ms | |].
- intros eff. fold ms. rewrite openat_check_head, (path_at_cstr p Hp).
rewrite (path_eqb_neq _ _ Hne), (openat_plain_name_noslash _ Hpl), (openat_plain_name_nodirref _ Hpl), Hfs.
apply check_copyins_after_open_result.
- intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
- intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
- intros e He. rewrite adv_set_epend. apply HA. exact He.
- rewrite adv_set_epend. exact HB.
Qed.
End Openat.
Lemma alloc_fd_init : ltac2:(TCodec.tc2 tcn__RefNodes "Q3'RA'H'XByR0%211&RI(:'C%1248(B&XAz%2291r3%54:>21+1%62=1r2%94>B21+2%:2A1r1%=4BF21(@%11@%C3A31%D3B81%E3C=1%G11+3%D2K1%N3K31p^:Q01p^8Q11p^6Q21").
Proof. intros. reflexivity. Qed.
Lemma fd_lookup_init_3 : ltac2:(TCodec.tc2 tcn__RefNodes "Q7'RA'H'A%113&RO(:'C'XByR0%211%421:(B&XAz%2261r3%547@21+1%62:1r2%94;D21+2%:2>1r1%=4?H21(@%11@%F3A31%G3B81%H3C=1+3%C2G1%L231(3%11Q2%Q23Q031p^:Q41p^8Q51p^6Q61").
Proof. intros. reflexivity. Qed.
Lemma rz_mmap_anon : ltac2:(TCodec.tc2 tcn__RefNodes "U@&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r6%3221(6r3%22;1%93841'9&QKr4%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r7%211(@%116%O3631&U6r;(X@+A(F%33QD21%6251&XA+VN%22QF1%Q:3QF41r<+;%;3QL19%>231%82QLD%Q@3QL21'G&V<zr8%3221&V@+2+R0%3221%8261%:261r>+<%L3R=1J%O231+3%J2R>1%R23R>31r?+=%Q33RD1Q1%Q6231+Q2%Q12RE1%R93RE31r@+>%Q:3RK1Q8%Q=231-1%Q82RL1%R@3RL31rA+?%QA3S21Q?%QD231%Q>2S2Q2%RF3S221&R9vX=%211(;%RK3RA21&SA%11Q1'I&U1rE+:%R03SA1QN%R3231rBr1r2%844321%S83RN1RJq]8SE1%<2SF1rF%R<21:rC%?4219S7%S?3S51S1'V5(R7&U7vW9&U9rG%231D@&U;+4%22>1&U5%RD2T8S?%23F1L&U:%11SK%=5<9631&U2rD%23L71%B241%D4T1Q<1QCp0F1p]8TB1%E5DLQ769%G21K%I4T6QA1QOp041p0Q11t`2T>Q?1p0QB1p0QH1p0QO1p0R71p0R?1p0RG1p0S31p0S:1p0SF1p0T11p0T81p0T?1pR@TJ1p_:TL1paDTN1p_LU11p_HU31p`:U:1p`BU:1").
Proof.
intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Halloc n Hex HB.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (Hargs : mmap_args_ok ms).
{ unfold mmap_args_ok, ms.
rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
destruct Hex as (a0 & Ha0).
eapply (srz_mmap segs scfg ms model (getr regs 17) KB Hh Hlazy eq_refl
ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc).
- intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
- rewrite H0, Hu1. exists a0. exact Ha0.
Qed.
Lemma rz_mmap_anon_nogrant : ltac2:(TCodec.tc2 tcn__RefNodes "TO&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r6%3221(6r3%22;1%93841'9&QKr4%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r7%211(@%116%O3631&U6r;(X@+A(F%33QD21%6251&XA+VN%22QF1%Q:3QF41r<+;%;3QL19%>231%82QLD%Q@3QL21'G&V<zr8%3221&V@+2+R0%3221%8261%:261r>+<%L3R=1J%O231+3%J2R>1%R23R>31r?+=%Q33RD1Q1%Q6231+Q2%Q12RE1%R93RE31r@+>%Q:3RK1Q8%Q=231-1%Q82RL1%R@3RL31rA+?%QA3S21Q?%QD231%Q>2S2Q2%RF3S221&U1rC+:%QH3S91QF%QK231r1&SA%11Q2%844E31(;%S13RG21p]8S>1'V5vX=(R7&U7vW9&U9&RL&R?%211%43DB1&U;rB+4%3221&U:%11S?%=5<73Q21%?21Q:r=%C4SCB21rD%B5A1Q0:6%D21Q8%G4SGF1QNp051p0J1p0Q71p0Q>1p0QF1p0QN1p0R61p0RB1p0RI1p0S51p0S@1p0SG1p0SN1pR>T91p_:T;1paDT=1p_LT@1p_HTB1p`:TI1p`BTI1").
Proof.
intros regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng HA.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
assert (Hargs : mmap_args_ok ms).
{ unfold mmap_args_ok, ms.
rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
eapply (srz_mmap_nogrant segs scfg ms model (getr regs 17) KA Hh Hlazy eq_refl
ltac:(rewrite H17; apply u64_lit; lia) Hargs).
- rewrite H0, Hu1. exact Hng.
- unfold ms. rewrite adv_set_epend. exact HA.
Qed.
Lemma srz_munmap : ltac2:(TCodec.tc2 tcn__RefNodes "TF&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r7%3221(6r4%22;1%93841'9&QKr5%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r8%211(@%116%O3631&U6r<(X@+A(F%33QD21%6251&XA+VG%22QF1%Q:3QF41r=+:%;3QL19%>231%Q?3QK1D&V=&XEr9%22R01&SB%5221z%QG3QI21r?+;%H3R91F%K231%E2R9:%QM3R921&V<r:%22:1&V;&V:%B2R@Q2&SAr;%211%5241&RF%8221&S;&T0&S9%11E%311%;1Q>%Q92RM1%733Q61%RB3R81R4'V5vX=(R7&U7vW9&U9rC%QC2S7Q4%332Q>1&U;rB+4%3221&U4r>%N1QG%QL2S@1rA%53421&U:%11S4%B5A=931&U3r@%23:81%G241%J4S:I1R<rD%I5H1FB8%K21<%N4S>M1R6p051p0Q11p0Q;1p0QE1p0QI1p0R01p0R91p0R?1p0RK1p0S61p0S=1p0SD1pR<SO1p_:T11p]8T<1paDT41p_LT71p_HT91p`:T@1p`BT@1").
Proof.
intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
eapply (SpinAlg.srz_munmap segs scfg ms model (getr regs 17));
[exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.
Lemma munmap_model_simple : ltac2:(TCodec.tc2 tcn__RefNodes "QO'XByR0%211'RD'H'='C%1255%311&S7r1%211(@%116%:3631%:1=&S8r2%211%71A%@3521&U3r5r4r3%43321&T7(S@&T3&S9%116%311&S<&T0%114%321=&S=&T2%118&XE%12Q7B&V:%32Q9C%2231%83641&T4%11@&SK%11B&SN%11D&T1%11F&SM%11H%L8HD;97531%N21Q0%QE3QFQ01p0Q61p0Q=1p_@QI1p`2QK1p]8QL1").
Proof.
intros a n m Hl Hm. unfold munmap_model, with_mmap_destroyed.
apply vm_forget_range_id; [rewrite with_vmmaps_lazy'; exact Hl | exact Hm].
Qed.
Definition brk_eff (ms : machine_state) (model : Model) (r : word) : SyscallEffect :=
mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [].
Definition brk_adm (model : Model) (req r : word) : Prop :=
brk_resolution_ok model req r
/\ (sc_alloc scfg = false -> brk_refusal_b model req r = true ->
forall r', brk_resolution_ok model req r' -> brk_refusal_b model req r' = true).
Lemma brk_r_ok_cases : ltac2:(TCodec.tc2 tcn__RefNodes "G'RD'XByR0%211&TMr3r2r1%43321'L'H&SK&S9r4%211%411%63=:1%73>;<%9221p0;1p`>A1p`DB1p_@F1").
Proof.
intros m req r H. unfold brk_resolution_ok, Mmap.brk_r_ok in H. cbv zeta in H.
destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m)))%Z)%bool.
- left. apply bv_eqb_eq. exact H.
- destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
+ apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
+ apply andb_true_iff in H as [H _]. apply orb_true_iff in H as [H|H]; apply bv_eqb_eq in H; auto.
Qed.
Lemma refusal_b_brk_ms : ltac2:(TCodec.tc2 tcn__RefNodes "Q0'QL'XByR0%211'RD'H'Q4&XEr3%2271+VF%63521'9&R8&R:vX>r5r4%43321r2%732<1&R4&QM(4%2281%43A16%E3>61p0@1p`>I1p_LI1paJK1p_NO1").
Proof.
intros ms x8 model r Hno. rewrite (refusal_b_brk (sys_input segs ms x8) model r)
by (rewrite in_sysno_sys_input; exact Hno).
rewrite in_arg0_sys_input214. reflexivity.
Qed.
Lemma node_brk : ltac2:(TCodec.tc2 tcn__RefNodes "S2'QL'RD'XByR0%211'H'A%113&S5r2%211(3%118%83631'='C%12<<%311&S7r3%211(@%116%B3631&QNr5%211(6%12H9%H3F31'Q4&XEr4%22N1+VF%N3521&V1vX>vX=(R7r7r6%3221'Q2&U@&QMr8(4%3221r1%63:21q`>Q?1%92Q@1'RM%Q111q031&R2&R3(S?&Q1r9%@21>%B3@1=q`>QK1%53QL1?y8%R011%QE11%QE2R01%Q@11&T>&SK&S9%11Q1%311%53K;1&T=%12=3'RC%QJ11'>%R22R=1%QM11%I6C>8641%K2Q61%M11&TL%13Q7GQ?%QA231q^LQ51%QF6QEQDQ@Q6Q31p0QH1p0QO1p0R61p0RA1paJRK1p_LRO1p_NS11").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno.
set (req := ms_gpr ms 0).
assert (Hshape : forall r, brk_resolution_ok model req r ->
m_halted (brk_model req r model) = None /\ m_vm_lazy (brk_model req r model) = []).
{ intros r Hr.
destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno (brk_ok_intro segs ms x8 model r Hno Hr))
as (_ & Hh' & _ & _ & Hlazy'). rewrite Hlazy in Hlazy'. split; assumption. }
apply (node_svc segs scfg ms model x8 {r : word | brk_adm model req r}
(fun i => brk_eff ms model (proj1_sig i))
(fun i => brk_model req (proj1_sig i) model)
(fun _ => []) Hh Hsvc).
- intros [r [Hr Hf]]. cbn [proj1_sig]. apply (brk_ok_intro segs ms x8 model r Hno Hr).
- intros [r [Hr Hf]]. cbn [proj1_sig].
destruct (sc_alloc scfg) eqn:Ealloc.
+ apply not_spurious_on. rewrite (injected_family_off_alloc scfg _ 214%Z);
[rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
+ destruct (brk_refusal_b model req r) eqn:Eref.
* apply not_spurious_forced. intros eff' m' evs' Hspec.
apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hspec.
destruct Hspec as (_ & _ & Hok' & _).
rewrite (refusal_b_brk_ms ms x8 model _ Hno). apply (Hf eq_refl eq_refl). exact Hok'.
* apply not_spurious_nonrefusal. unfold brk_eff. cbn [eff_ret].
rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
- intros eff m' ev Hspec.
pose proof (proj1 (brk_ok_iff segs ms x8 model eff m' ev Hno) Hspec) as (Heff & -> & Hok & ->).
fold req in Heff, Hok.
assert (Hmem : brk_adm model req (eff_ret eff) ->
exists i : {r : word | brk_adm model req r},
eff = brk_eff ms model (proj1_sig i) /\ brk_model req (eff_ret eff) model = brk_model req (proj1_sig i) model /\ ([] : list event) = []).
{ intros Hadm. exists (exist _ (eff_ret eff) Hadm). cbn [proj1_sig]. unfold brk_eff.
split; [exact Heff | split; reflexivity]. }
destruct (sc_alloc scfg) eqn:Ealloc.
+ left. apply Hmem. split; [exact Hok | intros E; rewrite Ealloc in E; discriminate E].
+ destruct (brk_refusal_b model req (eff_ret eff)) eqn:Eref.
*
assert (Hrq : negb (w_is0 req) = true /\ (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps model)))%Z = false
/\ bv_eqb req (vm_brk (m_vmmaps model)) = false /\ eff_ret eff = vm_brk (m_vmmaps model)).
{ unfold brk_refusal_b in Eref. cbv zeta in Eref.
apply andb_true_iff in Eref as [Eref E4]. apply andb_true_iff in Eref as [Eref E3].
apply andb_true_iff in Eref as [E1 E2].
apply negb_true_iff in E2. apply negb_true_iff in E3. apply bv_eqb_eq in E4. auto. }
destruct Hrq as (E1 & E2 & E3 & E4).
destruct (Mmap.brk_r_ok model req req) eqn:Egrant.
-- right. split; [| apply (proj1 (Hshape _ Hok))].
apply (spurious_intro scfg (sys_input segs ms x8) model eff (brk_eff ms model req)
(brk_model req req model) []).
++ rewrite (injected_family_off_alloc scfg _ 214%Z);
[rewrite Ealloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
++ rewrite (refusal_b_brk_ms ms x8 model _ Hno). exact Eref.
++ apply (brk_ok_intro segs ms x8 model req Hno). exact Egrant.
++ unfold brk_eff. cbn [eff_ret]. rewrite (refusal_b_brk_ms ms x8 model _ Hno).
unfold brk_refusal_b. cbv zeta. fold req. rewrite E3. apply andb_false_r.
-- left. apply Hmem. split; [exact Hok|]. intros _ _ r' Hr'.
destruct (brk_r_ok_cases model req r' Hr') as [-> | ->].
++ unfold brk_refusal_b. cbv zeta. fold req. rewrite E2, E3, bv_eqb_refl.
destruct (w_is0 req); [discriminate E1 | reflexivity].
++ unfold brk_resolution_ok in Hr'. rewrite Egrant in Hr'. discriminate Hr'.
* left. apply Hmem. split; [exact Hok|]. intros _ E. rewrite Eref in E. discriminate E.
- apply brk_no_unmodeled. exact Hno.
- intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj1 (Hshape r Hr)).
- intros [r [Hr Hf]]. cbn [proj1_sig]. apply (proj2 (Hshape r Hr)).
Qed.
Lemma brk_adm_query : ltac2:(TCodec.tc2 tcn__RefNodes "E'RD'XByR0%211&J&U@r2&XAz%2271r1%63521'H&SK&S9%119%311%53>71%>271p`>@1p_LD1").
Proof.
intros model r. unfold brk_adm, brk_resolution_ok, Mmap.brk_r_ok, brk_refusal_b. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb negb andb]. rewrite bv_eqb_eq. split.
- intros [H _]. exact H.
- intros H. split; [exact H | intros _ E; discriminate E].
Qed.
Lemma srz_brk_query_at : ltac2:(TCodec.tc2 tcn__RefNodes "RF'QL'RD'XByR0%211&V0'H'A%114&S5r3%211(3%119%83631'='C%12==%311&S7r4%211(@%116%B3631&QNr6%211(6%12I9%H3F31'Q4&XEr5%22O1+VF%N3521&QMr8(4%3221&XAz%22Q81%Q63Q841'V5vX>vX=(R7&R2&R3r9(S?&SK&S9%11A%311y8%QH11%Q<11%Q<2QH1%Q711'RC%Q911'>%QA2QM1%Q<11%?6;6Q<Q<41%B2A1%D11%F21Q0%J4IH1Q=r:%I21Fr7%N4ML21p051p0Q11p0Q:1p0QA1p0QH1p0R31pR<R=1paJR?1p_LRC1p_NRE1").
Proof.
intros ms model x8 K Hh Hlazy Hsvc Hno H0 Hc.
assert (Hq : brk_adm model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (rewrite H0; apply brk_adm_query; reflexivity).
apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ _ Hq) (node_brk ms model x8 Hh Hlazy Hsvc Hno)).
intros [r Hr]. cbn [proj1_sig].
assert (Er : r = vm_brk (m_vmmaps model)) by (apply (brk_adm_query model); rewrite <- H0; exact Hr). subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
exact Hc.
Qed.
Lemma rz_brk_query : ltac2:(TCodec.tc2 tcn__RefNodes "S9&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11&V0'H%:13&QJvX>r5%3221(6r2%22:1%93841'9&QKr3%211(E%?3521%I1K&S5%11>(3%11O%E3531'='C%12Q3Q3%311&S7r6%211(@%116%O3631&U6r:(X@+A(F%33QC21%6251&XA+VF%22QE1%Q:3QE41r;+:%;3QK19%>231z%92QL1%QA3QL31'V5vX=(R7&U7vW9&U9r<&SK&S9r9%211%411%736A1&U;+4%22F1&U:%11R0%?5>63Q31%A21:r7%E4R4D21r=%D5C1AN6%F21Q9r8%J4R9I21p061p0M1p0Q51p0QA1p0QL1p0R31p0R:1pR<RE1paDRG1p_LRJ1p_HRL1p`:S31p`BS31").
Proof.
intros regs pc mem model w K HF HE Hh Hlazy H17 H10 Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply (srz_brk_query_at _ model (getr regs 17));
[exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia
| rewrite ms_gpr_epend0; exact H10 |].
rewrite adv_ret_epend. exact Hc.
Qed.
Lemma brk_r_ok_grow_cases : ltac2:(TCodec.tc2 tcn__RefNodes "QE'RD'XByR0%211'RG&S9r3%211&V<z&XE%1295%4231&V;&T4r2%211%72?1r4%92A1%7231&SK%11@%=2E1r5%?2G1%=231&J&TMr7r6%33217'L'H%=1@%23Q0;1'G%43Q2=7'9&T<%13;::(E%93421%7261%<291%B2>1p0D1p0K1p0Q41t^FQ=Q:1p`>Q?1p`DQ@1p_@QD1").
Proof.
intros m req r h Hpos Hs Hb.
unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
assert (E0 : w_is0 req = false).
{ unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite E0. unfold min_brk.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
rewrite (proj2 (Z.ltb_ge _ _)) by lia.
rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
- intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
- intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.
Lemma brk_adm_grow_cases : forall m req r,
let h := m_vmmaps m in
sc_alloc scfg = false ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
(bv_unsigned (vm_brk h) < bv_unsigned req)%Z ->
brk_adm m req r <->
r = (if Mmap.brk_grow_ok m req req then req else vm_brk h).
Proof.
intros m req r. cbv zeta. intros Halloc Hs Hb.
set (b := vm_brk (m_vmmaps m)) in *.
pose proof (proj1 (bv_unsigned_in_range 64 b)) as Hb0.
assert (Hpos : (0 < bv_unsigned req)%Z) by lia.
assert (Hble : (bv_unsigned b <= bv_unsigned req)%Z) by lia.
assert (Hneq : bv_eqb req b = false).
{ apply bv_eqb_neq. intros E. rewrite E in Hb. lia. }
assert (Href : forall r', brk_refusal_b m req r' = bv_eqb r' b).
{ intros r'. unfold brk_refusal_b. cbv zeta. fold b. unfold min_brk.
replace (w_is0 req) with false
by (symmetry; unfold w_is0, bv_eqb; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; apply Z.eqb_neq; lia).
rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite Hneq. reflexivity. }
pose proof (fun r' => brk_r_ok_grow_cases m req r' Hpos Hs Hble) as Hcases. cbv zeta in Hcases. fold b in Hcases.
unfold brk_adm. rewrite (Hcases r).
destruct (Mmap.brk_grow_ok m req req) eqn:Eg; split.
- intros [[-> | [-> _]] Hf]; [| reflexivity].
exfalso.
assert (E1 : brk_refusal_b m req b = true) by (rewrite Href; apply bv_eqb_refl).
assert (E2 : brk_refusal_b m req req = true).
{ apply (Hf Halloc E1 req). apply (proj2 (Hcases req)). right. split; [reflexivity | first [exact Eg | reflexivity]]. }
rewrite Href, Hneq in E2. discriminate E2.
- intros ->. split; [right; split; [reflexivity | first [exact Eg | reflexivity]]|]. rewrite Href, Hneq. intros _ E. discriminate E.
- intros [[-> | [-> Habs]] _]; [reflexivity | rewrite ?Eg in Habs; discriminate Habs].
- intros ->. split; [left; reflexivity|]. intros _ _ r' Hr'. rewrite Href.
destruct (proj1 (Hcases r') Hr') as [-> | [-> Habs]]; [apply bv_eqb_refl | rewrite ?Eg in Habs; discriminate Habs].
Qed.
Lemma brk_model_keep : ltac2:(TCodec.tc2 tcn__RefNodes "@'RD'XByR0%211'H&TLr1&SK&S9r2%211%411%73613%93=14p`D;1p_@?1").
Proof.
intros m req. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next.
rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.
Lemma brk_model_grow_eq : ltac2:(TCodec.tc2 tcn__RefNodes "RB'RD'Q4'RG&S9r2%211'XByR0%211&SKr1%211&V<zr3%3221&XE%12:=%6251&V:%42=6r5%3221&V@+2+R0%3221%?251'H&V=r4%?2H1&SB%4221%63Q11Er7%7214%93Q41H&TL&XAr6%I2Q21r8%H221%52Q51r9%83221&T7(S@&T3%11?(:'C%12Q=Q=(B%@2Q@=%24Q@Q@@1&T0%11G%83631&T2%11J&T4%11L&SN%11N&T1%11Q0&SM%11Q2%F8D;97J531%H21J%Q<3R8J1p0Q41p0Q81p0Q@1p0QJ1p0QN1t]<R6R31t^FR=R:1p^0R?1p_@RA1").
Proof.
intros m d h b Hd Hb0 Hnw Hbal Hdal.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)).
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
unfold brk_model_next, brk_maps_next. fold b.
rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
cbn [app maps_subtract_ranges fold_left].
replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
apply bv_eq. rewrite bv_sub_unsigned, Hureq.
rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.
Lemma srz_brk_grow_at : ltac2:(TCodec.tc2 tcn__RefNodes "UI'QL'RD'XByR0%211'Q4&V0'H'A%115&S5r4%211(3%11:%83631'='C%12>>%311&S7r5%211(@%116%B3631&QNr7%211(6%12J9%H3F31&XEr6%22O1+VF%M3O21'9&R9vX=%211(;%Q33521'RG&S9r9%211&SKr1%211&V=%C2Q@3&SB%3221z%Q@3QB21r:%7215%QC3QE14&V<r;%2271%N2QKQC%4291&V:%Q12QNQ<r=%3221&V@+2+R0%3221%=251&V;&T4%11Q@%Q<2R91r>%>2Q<1%6231&QMrB(4%3221&XA%QE2RBQJr?%G221%42RE1%RB3RE61&T<r8%QL2RI1r@%N221%;2RL1%63?11%RJ3QL1QH'V5vX>(R7&R2&R3rD(S?y8%S811%RK11%RK2S81%RF11'RC%RH11'>%S02S=1%RK11%;6R66RKRK41%>2=1%@11rC%C221%F4ERA1Kp0H1%RJ2SGR=rA%QL221%Q92SJ1%Q43811(E%SI3RK21rE%S22SOR:%R321QB%Q@2T11(:(B%QC2T4QF%24T4T4R@1%43SG1SA%Q266M1SBKH%Q52:1%Q711&T7(S@&T3%11RD&T0%11RF%>3T1;1&T2%11RI%R<1RJ&SN%11RL&T1%11RN&SM%11S0%?8=:87I531%A21QG%QK2C1%QN4QMSI1Q5p0Q11%QN2Q1QK%R14R0SL1Q8p031p0Q<1p0R=1p0RH1p0S01p0S:1p0S=1p0SA1p0SE1t]<U9SL1t^FT3T01p0T51p0T<1p0TB1p0TI1p0U41pR<U>1p^0U@1paJUB1p_LUF1p_NUH1").
Proof.
intros ms model x8 d K Hh Hlazy Hsvc Hno Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H0 HA HB.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
assert (Hcases : forall r, brk_adm model (ms_gpr ms 0) r <-> r = (if Mmap.brk_grow_ok model req req then req else b)).
{ intros r. rewrite H0. apply (brk_adm_grow_cases model req r Halloc); fold h; fold b; rewrite Hureq; lia. }
set (r0 := if Mmap.brk_grow_ok model req req then req else b).
assert (Hr0 : brk_adm model (ms_gpr ms 0) r0) by (apply Hcases; reflexivity).
apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ r0 Hr0) (node_brk ms model x8 Hh Hlazy Hsvc Hno)).
intros [r Hr]. cbn [proj1_sig]. fold h.
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
destruct (Mmap.brk_grow_ok model req req) eqn:Eg.
-
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
unfold brk_page_range.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned req))
by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
apply HB. first [exact Eg | reflexivity].
-
fold b. rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
apply HA. first [exact Eg | reflexivity].
Qed.
Lemma rz_brk_grow : ltac2:(TCodec.tc2 tcn__RefNodes "V?&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r6%3221(6r3%22;1%93841'9&QKr4%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r7%211(@%116%O3631&U6r;(X@+A(F%33QD21%6251&XA+VF%22QF1%Q:3QF41&R9vX=%211(;%Q?3Q521'RG&S9r:%211&SKr1%211&V=&XE%12R64&SB%4221z%QM3QO21%72M4%QO3R113&V<r<%2261%;2R@QG%4281&V:r5%?2RD1r>%4221&V@+2+R0%3221%>251&V;&T4%11QF%J2RO1%K2S0R?r?%@221%7241rE+:%QG3S81QE%QJ231%Q32S8R0r@%H221%QG2S;1%RO3S;51&T<rCr8%Q;2S@1rA%Q0221%QO2SC1%73611%S83RN1QJ'V5(R7&U7vW9&U9rGr9%332G1&U;rF+4%3221&U:%11SC%<5;73Q01rD%?221%A4SGR>1Fp0C1%R42T9=rB%QI221%RH2T<1%Q03811%T13SG1SCrH%R;2T@RA%QO21Q3%RN2TB1%I34Q=1%F2ID&U5%S22TFQ8%23RH1H%Q05O541E&T7(S@&T3%11S>(:(B%14TNTNS09&T0%11SC%53SM31&T2%11SF%R81SG&SN%11SI&T1%11SK&SM%11SM%B8@:87J531%D21R9%QG2F1%QI4TOSF1Q5p0Q21%QI5QHQ2QFQBQ>%QK21R>%QM4U3SJ1Q9p041p0Q=1p0R:1p0RD1p0RM1p0S81p0S;1p0S?1p0SB1t]<ULSJ1t^FT1SN1p0T31p0T91p0TE1p0U01p0U71p0U>1pR<UI1p^0UK1paDUM1p_LV01p_HV21p`:V91p`BV91").
Proof.
intros regs pc mem model w d K HF HE Hh Hlazy H17 Halloc h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
apply (srz_brk_grow_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) d K
Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc Hbal Hdal Hd Hb0 Hnw Hs
ltac:(rewrite ms_gpr_epend0; exact H10)).
- intros Eg. rewrite adv_ret_epend. apply HA. exact Eg.
- intros Eg. rewrite adv_zeros1_epend. apply HB. exact Eg.
Qed.
Lemma errno_ret_in_mmap : ltac2:(TCodec.tc2 tcn__RefNodes "@'XByR0%211'H'9&QF&T?r1%3221&TG&RL&R?%211%43<61%;3:61p`>=1").
Proof. intros r. unfold errno_ret_in, mmap_errnos. cbn [existsb]. apply orb_false_r. Qed.
Lemma errno_ret_in_mprotect : ltac2:(TCodec.tc2 tcn__RefNodes "@'XByR0%211'H'9&QF&TAr1%3221&TG&RL&R?%211%43<61%;3:61p`>=1").
Proof. intros r. unfold errno_ret_in, mprotect_errnos. cbn [existsb]. apply orb_false_r. Qed.
Lemma node_chk_grant_only : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
injected_family_off scfg (sys_input segs ms x8) = true ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(exists i, eff = effs i /\ m' = ms' i /\ evs = [])
\/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok segs scfg (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' i0 Hh Hsvc Hoff Hok Hnr Hinv Hnu Hh' Hlazy.
apply (node_chk_sp segs scfg ms model x8 I effs ms' Hh Hsvc Hok).
- intros i. apply not_spurious_nonrefusal. apply Hnr.
- intros eff m' evs Hc. destruct (Hinv eff m' evs Hc) as [Hm | [Hr Hhm]]; [left; exact Hm | right].
split; [| exact Hhm].
apply (spurious_intro scfg _ model eff (effs i0) (ms' i0) []); [exact Hoff | exact Hr | | apply Hnr].
apply check_syscall_ok_iff. apply Hok.
- exact Hnu.
- exact Hh'.
- exact Hlazy.
Qed.
Lemma injected_family_off_222 : ltac2:(TCodec.tc2 tcn__RefNodes "N'QL'XByR0%211'H'Q4&XEr1%2261+VN%63521'9&R9vX=%211(;%<3521&R6&R:vX>r4r3%43321%62:1(E%E3>21p0:1p0A1paJI1p_NM1").
Proof.
intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 222%Z);
[rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto].
Qed.
Lemma injected_family_off_226 : ltac2:(TCodec.tc2 tcn__RefNodes "N'QL'XByR0%211'H'Q4&XEr1%2261+W2%63521'9&R9vX=%211(;%<3521&R6&R:vX>r4r3%43321%62:1(E%E3>21p0:1p0A1paJI1p_NM1").
Proof.
intros ms x8 Hno Halloc. rewrite (injected_family_off_alloc scfg _ 226%Z);
[rewrite Halloc; reflexivity | rewrite in_sysno_sys_input; exact Hno | auto 6].
Qed.
Definition noaccess_model (a n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
((a, n) :: vm_maps (m_vmmaps m))
((a, n) :: vm_noaccess (m_vmmaps m))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Lemma grant_ok_grant_ok_na : ltac2:(TCodec.tc2 tcn__RefNodes "H'XByR0%211'RD'Q4'H'9&U1r4r3r2r1%544321(E%93821&UCr5%241987%=3<15p051p`2@1p]8C1p_@C1p^JE1").
Proof.
intros hint m a n H. unfold grant_ok in H. unfold grant_ok_na.
apply andb_true_iff in H as [H _]. exact H.
Qed.
Lemma grant_ok_na_unpack : ltac2:(TCodec.tc2 tcn__RefNodes "QF'XByR0%211'RD'Q4'H'9&UCr4r3r2r1%544321(E%93821'G&V=&XE%12A9&SB%4221z%A3B21&V<%1236&V;&V:%129A&RJ&S9%11F%311%7251&SE&8'C%12Q2Q2&T3%118&T0%11:%73531&XA%12Q:Q1%;33Q31%Q83Q71Q0%O2>1%Q02G1%Q12J1p0Q31p`2Q>1p]8QA1p_@QA1p^JQC1").
Proof.
intros hint m a n H. unfold grant_ok_na in H.
rewrite !andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto.
Qed.
Lemma grant_na_not_errno : ltac2:(TCodec.tc2 tcn__RefNodes "N'XByR0%211'RD'Q4&V;zr1%3221'H'9&UCr5r4r3r2%544321(E%93821&QF&T?%2218(;%>3=21p061p0A1p`2F1p]8I1p_LI1p^JK1").
Proof.
intros hint model a n Hn Hg. destruct (grant_ok_na_unpack _ _ _ _ Hg) as (_ & _ & Htop & _).
apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Definition mmap_noaccess_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
/\ ms_gpr ms 3 = Z_to_bv 64 34 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_noaccess_check : forall ms x8 model eff,
bv_unsigned x8 = 222%Z -> mmap_noaccess_args_ok ms ->
check_syscall (sys_input segs ms x8) eff model
= let n := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)]
then CheckOk (noaccess_model r (Z_to_bv 64 n) model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff Hno (H1 & H2 & H3 & H4 & H5).
rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
rewrite E1, H2, H3, H5.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 34)) with true by (vm_compute; reflexivity).
replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with false
by (vm_compute; reflexivity).
replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 34) (Z_to_bv 64 0)) with true
by (vm_compute; reflexivity).
cbn [negb]. cbv beta iota zeta.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
destruct (errno_ret_in mmap_errnos r); [reflexivity|].
unfold grant_ok_na, noaccess_model, with_mmap_backing.
replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
rewrite <- !andb_assoc. reflexivity.
Qed.
Lemma node_mmap_noaccess : ltac2:(TCodec.tc2 tcn__RefNodes "SK'QL'RD'XByR0%211'H'A%113&S5r2%211(3%118%83631'='C%12<<%311&S7r3%211(@%116%B3631&QNr5%211(6%12H9%H3F31'Q4&XEr4%22N1+VN%N3521&UEr7%211'9&R9vX=%211(;%Q73521&SA&QMr9u1%3221%C2Q?1%611'I&UCr;(4%:221r:r1%64321QB(E%QH3F21q]8QJ1%;2QK1&V1vX>(R7%12=:'Q2r<%H21?%B41A=QD%R33Q11<q]8R51%62R61'RM%QG11q031&R2&R3(S?&Q1r=%Q521L%O41?JQD%R@3Q>1Iq]8RB1%63RC1My8%RG11%R<11%R<2RG1%R711(:(B&XA%12RMR=%34RMRM:1%53RB1R<'RC%R?11'>%RG2S21%RB11%H6A<RB641%J2Q41%L11&UG%13E<QF%Q;231q^LQ41%Q?6Q>R6Q<Q5Q21p0QA1t`2RCQN1p0R61p0R=1p0RA1p0RH1p0RO1p0S:1paJSD1p_LSH1p_NSJ1").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc n [a0 Ha0].
pose proof (fun eff => mmap_noaccess_check ms x8 model eff Hno Hargs) as Hchk. cbv zeta in Hchk. fold n in Hchk.
assert (Hn0 : (0 <= n)%Z) by (unfold n; apply page_round_up_Z_nonneg; apply (proj1 (bv_unsigned_in_range 64 _))).
apply (node_chk_grant_only ms model x8 {a : word | grant_ok_na (ms_gpr ms 0) model a n = true}
(fun i => mkEffectU (proj1_sig i) [] [] [(proj1_sig i, Z_to_bv 64 n)] [] [])
(fun i => noaccess_model (proj1_sig i) (Z_to_bv 64 n) model)
(exist _ a0 Ha0) Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
- intros [a Ha]. cbn [proj1_sig]. rewrite Hchk, (grant_na_not_errno _ _ _ _ Hn0 Ha), Ha.
cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros [a Ha]. cbn [proj1_sig eff_ret].
rewrite (refusal_b_mmap (sys_input segs ms x8) model a) by (rewrite in_sysno_sys_input; exact Hno).
rewrite <- errno_ret_in_mmap. exact (grant_na_not_errno _ _ _ _ Hn0 Ha).
- intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Er.
+ destruct us; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
rewrite (refusal_b_mmap (sys_input segs ms x8) model r) by (rewrite in_sysno_sys_input; exact Hno).
rewrite <- errno_ret_in_mmap. split; [exact Er | exact Hh].
+ destruct (grant_ok_na (ms_gpr ms 0) model r n) eqn:Hg; [|discriminate].
destruct (listNN_eqb us [(r, Z_to_bv 64 n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
left. exists (exist _ r Hg). repeat split; reflexivity.
- intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
destruct (grant_ok_na (ms_gpr ms 0) model r n && listNN_eqb us [(r, Z_to_bv 64 n)])%bool; discriminate.
- intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh.
- intros [a Ha]; cbn [proj1_sig]. unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.
Lemma srz_mmap_noaccess_at : ltac2:(TCodec.tc2 tcn__RefNodes "SE'QL'RD'XByR0%211&V0'H'A%114&S5r3%211(3%119%83631'='C%12==%311&S7r4%211(@%116%B3631&QNr6%211(6%12I9%H3F31'Q4&XEr5%22O1+VN%N3521&UEr8%211'9&R9vX=%211(;%Q73521&SA&QMr:u1%3221%C2Q@1%611'I&UCr<(4%:221r;r1r2%744321(E%QI3G21q]8QL1%<2QM1r=%D21;%>41=9QJ%QO3M17'V5vX>(R7&R2&R3r>(S?y8%R<11%R011%R02R<1%QK11(:(B&XA%12RBR1%34RBRBJ1%53R61R0'RC%R311'>%R;2RG1%R611%A6Q1<R6641%D2C1%F11&UG%13Q5<O%J231%M4LQI1Q9p0O1p]8S11%N2Q4Q?%Q14Q0QM1QGp031p0Q81t`2R;QF1p0QN1p0R51p0R91p0R@1p0RG1p0S21pR<S<1paJS>1p_LSB1p_NSD1").
Proof.
intros ms model x8 K Hh Hlazy Hsvc Hno Hargs Halloc n Hex HK.
destruct Hex as [a0 Ha0].
apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ a0 Ha0)
(node_mmap_noaccess ms model x8 Hh Hlazy Hsvc Hno Hargs Halloc (ex_intro _ a0 Ha0))).
intros [a Ha]. cbn [proj1_sig]. apply HK. exact Ha.
Qed.
Lemma rz_mmap_noaccess : ltac2:(TCodec.tc2 tcn__RefNodes "U>&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r6%3221(6r3%22;1%93841'9&QKr4%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r7%211(@%116%O3631&U6r;(X@+A(F%33QD21%6251&XA+VN%22QF1%Q:3QF41r<+;%;3QL19%>231%82QLD%Q@3QL21'G&V<zr8%3221&V@+2+R0%3221%8261%:261r>+<%L3R=1J%O231%I2R==%R13R=21r?+=%Q23RC1Q0%Q5231+Q2%Q02RD1%R83RD31r@+>%Q93RJ1Q7%Q<231-1%Q72RK1%R?3RK31rA+?%Q@3S11Q>%QC231%RD3S01D&R9vX=%211(;%RI3R?21&SA%11O'I&UCrE+:%QN3S?1QL%R1231rBr1r2%844321%S63RL1RHq]8SC1%<2SD1rF%R:21:rC%?4219S5%S=3S31RO'V5(R7&U7vW9&U9rG%231D@&U;+4%22>1&U4%RB2T6S=%23F1L&U:%11SI%=5<9631&UGrD%23L71%B241%D4SOQ<1QBp0F1p]8T@1%E5DLQ769%G21K%I4T4QA1QNp041p0Q11t`2T<Q?1p0QB1p0QH1p0QN1p0R61p0R>1p0RE1p0S11p0S81p0SD1p0SO1p0T61p0T=1pR@TH1p_:TJ1paDTL1p_LTO1p_HU11p`:U81p`BU81").
Proof.
intros regs pc mem model w len KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Halloc n Hex HB.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
assert (Hargs : mmap_noaccess_args_ok ms).
{ unfold mmap_noaccess_args_ok, ms.
rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
pose proof (srz_mmap_noaccess_at ms model (getr regs 17) KB Hh Hlazy eq_refl
ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc) as H.
cbv zeta in H. rewrite Hu1, H0 in H. fold n in H. apply H; [exact Hex|].
intros a Ha. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.
Definition mprotect_model (addr n : word) (m : Model) : Model :=
with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.
Lemma mprotect_model_next_eq : ltac2:(TCodec.tc2 tcn__RefNodes "@'RD'XByR0%211'H&TBr3r2r1%43321&UF%13435%83<31p`2:1p]:;1p_@?1").
Proof. reflexivity. Qed.
Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
bv_unsigned x8 = 226%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
ms_gpr ms 2 = Z_to_bv 64 3 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mprotect_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
then CheckOk (mprotect_model addr n model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
rewrite H0, H2, Hu1.
replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
destruct cs; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
destruct ci; [| destruct (errno_ret_in mprotect_errnos r); reflexivity].
reflexivity.
Qed.
Lemma ENOMEM_in_mprotect_errnos : ltac2:(TCodec.tc2 tcn__RefNodes "5&V7'Q4&R?&TA%43321").
Proof. left. reflexivity. Qed.
Lemma srz_mprotect_at : ltac2:(TCodec.tc2 tcn__RefNodes "TO'QL'RD'XByR0%211'Q4&V0'H'A%115&S5r5%211(3%11:%83631'='C%12>>%311&S7r6%211(@%116%B3631&QNr8%211(6%12J9%H3F31&XEr7%22O1+W2%M3O21'9&R9vX=%211(;%Q33521&QMr;(4%3221%Q83Q;1D&V=r9%B2Q?1&SB%4221z%Q?3QA21r=u1%>221&XA%12QH:%QE3QH31&V<r:%22:1&V:r<%Q22QO1&SA%11H%5231&SH%:221r@u2%O221+3%B2R91%R63R931%;1G%E2R<1&S:&T2&S9rA%211%411r?r1%83321(E%RC3QE21&T0rB%;11%311r2%@32H1%RJ3QL18&T@rCr3%332B1%RO3R11='V5vX>(R7&R2&R3rE(S?%QD2S;QIy8%S>11%S111%S12S>1%RL11(:(Br4%24SCSCK1%43S61S0'RC%S311'>%S;2SH1%S611%A6@;6S641%D2C1%F11&UFrD%23Q7=1%K241%N4MRN1QMrF%N21K%Q14Q0S11QEp041p0Q41p0Q:1p0QB1t`2T9QN1p0R11p0R81p0RA1p0RE1p0RL1p0S41p0S:1p0SA1p0SG1p0SN1p0T91pR<TC1p_:TE1p]:TG1paJTH1p_LTL1p_NTN1").
Proof.
intros ms model x8 addr len K Hh Hlazy Hsvc Hno Halloc H0 Hal H1 Hlen Hnw H2 n Hna Hma Hbud HK.
pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
apply (srz_cases1 segs scfg (mkCfg ms model) unit
(fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])))
(mprotect_model addr n model)) K tt).
2:{ intros []. exact HK. }
apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [])
(fun _ => mprotect_model addr n model) tt Hh Hsvc (injected_family_off_226 ms x8 Hno Halloc)).
- intros []. rewrite Hchk, errno_ret_in_mprotect.
replace (bv_eqb (Z_to_bv 64 0) (errno_ret ENOMEM)) with false by (symmetry; apply bv_eqb_neq; discriminate).
unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros []. cbn [eff_ret]. rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
apply bv_eqb_neq. discriminate.
- intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r) eqn:Er.
+ destruct zs; [|discriminate]. injection Hc as <- <-. right. cbn [eff_ret].
rewrite (refusal_b_mprotect (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
rewrite <- errno_ret_in_mprotect. split; [exact Er | exact Hh].
+ cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. left. exists tt. repeat split; reflexivity.
- intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
- intros []. unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh.
- intros []. unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.
Lemma rz_mprotect : ltac2:(TCodec.tc2 tcn__RefNodes "UA&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r7%3221(6r4%22;1%93841'9&QKr5%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r8%211(@%116%O3631&U6r<(X@+A(F%33QD21%6251&XA+W2%22QF1%Q:3QF41&R9vX=%211(;%Q?3Q521r>+:%@3R11>%C231r9%QE3R121&V=&XEr:%22R61&SB%5221z%QM3QO21r@+;%N3R?1L%Q1231%K2R?:%R33R?21&V<r;%22:1&V:r=%B2RF1&SA%11Q:%5231&SH%:221rC+<%Q?3S01Q=%QB231+3%Q=2S11%RE3S131%<1Q6%Q@2S41&S:&T2&S9rB%211%411r1%732Q11%S03RF1RB&T0%81C%211rAr2%>3321%S73RM1RI&T@rDr3%332@1%S<3S21RN'V5(R7&U7vW9&U9rH%R<2T0QG%332R21&U;rG+4%3221&U5rF%23Q<SD1&U:%11SJ%?5>:631&UFrE%23QBSJ1%D241%F4T0RG1OrI%F5E1C?8%H21<%J4T4RK1Q<p051p0M1p0Q31p0Q;1t`2THQE1p0QH1p0R01p0R91p0R=1p0RD1p0RM1p0S41p0S:1p0SF1p0T11p0T81p0T?1pR@TJ1p_:TL1p]:U71paDTO1p_LU21p_HU41p`:U;1p`BU;1").
Proof.
intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
apply (srz_mprotect_at (epend regs pc mem (seg_rom segs) (getr regs 17)) model (getr regs 17) addr len KB
Hh Hlazy eq_refl ltac:(rewrite H17; apply u64_lit; lia) Halloc
ltac:(rewrite ms_gpr_epend0; exact H10) Hal
ltac:(rewrite ms_gpr_epend1; exact H11) Hlen Hnw
ltac:(rewrite ms_gpr_epend2; exact H12) Hna Hma Hbud).
rewrite adv_zeros1_epend. exact HB.
Qed.
Lemma srz_mprotect_blocked_at : ltac2:(TCodec.tc2 tcn__RefNodes "TE'QL'RD'XByR0%211'Q4&V0'H'A%115&S5r5%211(3%11:%83631'='C%12>>%311&S7r6%211(@%116%B3631&QNr8%211(6%12J9%H3F31&XEr7%22O1+W2%M3O21&QMr:(4%3221%Q23Q518&V=%;2Q8@&SB%3221z%Q83Q:21r<u1%=221&XA%12QAI%Q>3QA31&V<r9%22:1&V:r;%K2QH1&SA%11G%5231&SH%:221r?u2%N221+3%B2R21%QO3R231%;1G%E2R51'9&S:&T2&S9r@%211%411r>r1%83321(E%R=3;21&T0rA%;11%311r2%@32I1%RD3B18&T@rBr3%332B1(;%RJ3H21'V5vX>vX=(R7&R2&R3rD(S?&RL&R?%211y8%S<11%RO11%RO2S<1%RJ11'RC%RL11'>%S42SA1%RO11%>6;6RORO41%A2@1%C11rC%F221%J4IH1QKrE%I21F%M4LK1QBp041p0Q01p0Q71p0Q?1t`2T0QL1p0QO1p0R61p0R?1p0RC1p0RJ1p0S11p0S71p0S=1p0SD1p0SO1pR<T91p_:T;1p]:T=1paJT>1p_LTB1p_NTD1").
Proof.
intros ms model x8 addr len K Hh Hlazy Hsvc Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma Hbud HK.
pose proof (fun eff => mprotect_check ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 Hna Hma) as Hchk.
cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk. cbn [andb] in Hchk.
eapply srz_silent1; [| exact HK].
apply (node_det segs scfg ms model x8 (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) model [] Hh Hsvc).
- intros [r ws zs us cs ci] m' evs. rewrite Hchk. split.
+ intros Hc. destruct ws; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r) eqn:Er; [|discriminate].
destruct zs; [|discriminate]. injection Hc as <- <-.
rewrite errno_ret_in_mprotect in Er. apply bv_eqb_eq in Er. subst r. repeat split; reflexivity.
+ intros (He & -> & ->). injection He as -> -> -> -> -> ->.
rewrite (errno_ret_in_intro _ _ ENOMEM_in_mprotect_errnos). reflexivity.
- intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate | discriminate].
- exact Hh.
- exact Hlazy.
Qed.
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
(with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
(maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
(vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).
Lemma fixed_noaccess_model_simple : ltac2:(TCodec.tc2 tcn__RefNodes "R1'XByR0%211'RD'H'='C%1255%311&S7r1%211(@%116%:3631%:1=&S8r2%211%71A%@3521&UBr5r4r3%43321&T7(S@&T3&S9%116%311&T0%113(:(B%14Q2Q2>=&S=&T2%119&XE%12Q8C&V:%32Q:D%2231%83641%<3Q7:1&T4%11B&SK%11D&SN%11F&T1%11H&SM%11J%N8JH;97531%Q021Q2%QG3QHQ21p0Q81p0Q?1p_@QK1p`2QM1p]:QN1").
Proof. intros. unfold fixed_noaccess_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.
Lemma fixed_destroyed_model_simple : ltac2:(TCodec.tc2 tcn__RefNodes "QN'XByR0%211'RD'H'='C%1255%311&S7r1%211(@%116%:3631%:1=&S8r2%211%71A%@3521&UAr5r4r3%43321&T7(S@&T3&S9%116%311&S=&T0%114&XE%12Q3>&V:%32Q5?%2231%83641&T2%11<%;3174&T4%11?&SK%11A&SN%11C&T1%11E&SM%11G%K8G>;97531%M21O%QD3QEO1p0Q51p0Q<1p_@QH1p`2QJ1p]:QK1").
Proof. intros. unfold fixed_destroyed_model. apply vm_forget_range_id; [rewrite with_vmmaps_lazy'|]; assumption. Qed.
Definition mmap_fixed_args_ok (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 0
/\ ms_gpr ms 3 = Z_to_bv 64 50 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with
| [] => CheckOk model []
| _ => if listNN_eqb us [(addr, n)]
then CheckOk (fixed_destroyed_model addr n model) []
else CheckReject
end
else if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (fixed_noaccess_model addr n model) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H1' Hlen Htop n Hrf Hmc.
pose proof (u64_range addr) as Har.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1'; apply u64_lit; lia).
rewrite (mmap_check ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
rewrite E1, H2, H3, H5, H0, Hu1.
replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
replace (mmap_anon_b (Z_to_bv 64 50)) with true by (vm_compute; reflexivity).
replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
by (vm_compute; reflexivity).
replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
by (vm_compute; reflexivity).
replace (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true
by (vm_compute; reflexivity).
cbn [negb]. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
unfold fixed_noaccess_model, fixed_destroyed_model, with_mmap_replacement, with_mmap_backing, with_mmap_destroyed.
replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
reflexivity.
Qed.
Lemma srz_mmap_fixed_noaccess_at : ltac2:(TCodec.tc2 tcn__RefNodes "TN'QL'RD'XByR0%211'Q4&V0'H'A%115&S5r5%211(3%11:%83631'='C%12>>%311&S7r6%211(@%116%B3631&QNr8%211(6%12J9%H3F31&XEr7%22O1+VN%M3O21&UDr:%211'9&R9vX=%211(;%Q63521&QMr<(4%3221r9%Q<3Q?21&V=%E2QB?&SB%3221z%QB3QD21&V<r;%L2QI1%3251r?u1%B221&XA%12QO7%QL3QO31%:2<E&V;&V:r>%Q82R51&SAr=%211%6241&RJ&S9r@%211%411%=261%:1<%C2RA1&SE&T3rB%:11%311r1%632<1(E%RF3QE21&S:&T0rC%C11%311rAr2%73321%RO3QN1:'V5vX>(R7&R2&R3rE(S?y8%S=11%S011%S02S=1%RK11(:(Br3%24SBSBO1%43S51RO'RC%S211'>%S:2SG1%S511%@6Q6;S5641%C2B1%E11&UBrD%23Q;=1%J241%M4LRJ1QErF%M21J%Q04ORM1Q4p041p0Q31p0Q=1t`2T7QG1p0QJ1p0R91p0R;1p0RB1p0RG1p0RN1p0S51p0S<1p0S@1p0SF1p0SM1p0T81pR<TB1p_:TD1p]:TF1paJTG1p_LTK1p_NTM1").
Proof.
intros ms model x8 addr len K Hh Hlazy Hsvc Hno Hargs Halloc H0 Hal Hpos H1 Hlen Htop n Hrf Hmc HK.
pose proof (fun eff => mmap_fixed_check ms x8 model eff addr len Hno Hargs H0 Hal Hpos H1 Hlen Htop Hrf Hmc) as Hchk.
cbv zeta in Hchk. fold n in Hchk.
assert (Hne : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|].
pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
apply (srz_cases1 segs scfg (mkCfg ms model) unit
(fun _ => mkCfg (advance_past_svc (apply_effect ms (mkEffectU addr [] [] [(addr, n)] [] [])))
(fixed_noaccess_model addr n model)) K tt).
2:{ intros []. exact HK. }
apply (node_chk_grant_only ms model x8 unit (fun _ => mkEffectU addr [] [] [(addr, n)] [] [])
(fun _ => fixed_noaccess_model addr n model) tt Hh Hsvc (injected_family_off_222 ms x8 Hno Halloc)).
- intros []. rewrite Hchk, Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros []. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
rewrite <- errno_ret_in_mmap. exact Hne.
- intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Er.
+ right. cbn [eff_ret]. rewrite (refusal_b_mmap (sys_input segs ms x8)) by (rewrite in_sysno_sys_input; exact Hno).
rewrite <- errno_ret_in_mmap. split; [exact Er|].
destruct us; [injection Hc as <- <-; exact Hh|].
destruct (listNN_eqb _ _); [|discriminate]. injection Hc as <- <-.
unfold fixed_destroyed_model. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh.
+ destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. injection Hc as <- <-.
left. exists tt. repeat split; reflexivity.
- intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; [discriminate | destruct (listNN_eqb _ _); discriminate]|].
destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
- intros []. unfold fixed_noaccess_model. rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
- intros []. unfold fixed_noaccess_model. apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
Qed.
Lemma rz_mmap_fixed_noaccess : ltac2:(TCodec.tc2 tcn__RefNodes "V7&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4&V0'H%;14&QJvX>r7%3221(6r4%22;1%93841'9&QKr5%211(E%?3521%J1L&S5%11>(3%11Q0%E3531'='C%12Q4Q4%311&S7r8%211(@%116%O3631&U6r<(X@+A(F%33QD21%6251&XA+VN%22QF1%Q:3QF41&R9vX=%211(;%Q?3Q521r>+:%@3R11>%C231r9%QE3R121&V=&XEr:%22R61&SB%5221z%QM3QO21&V<r;%92R=1%3251rA+;%Q23RC1Q0%Q5231%O2RC7%R73RC21%:2<Q7&V;&V:%D2RHK&SAr=%211%5241&RJ&S9r@%211%411%<261rD+<%QF3S71QD%QI231%QC2S7N%RK3S721rE+=%QL3S=1QJ%QO231+QB%QJ2S>1%S23S>31rF+>%R33SD1R1%R6231-1%R12SE1%S93SE31rG+?%R:3SK1R8%R=231%S>3SJ1DrB%Q411%R:2SN1&SE&T3%Q31A%211r1%532Q11%SH3S>1S:&S:&T0%Q:1A%211r2%532Q21%SO3SE1SA'V5(R7&U7vW9&U9rK%231RDQ3&U;rJ+4%3221&U4r3rI%33Q;21&U:%11T=%?5>;731&UBrH%23QA81%D241%F4TCS:1R0rL%F5E1C@8%H21<%J4TGS>1QNp051p0M1p0Q51t`2U:Q=1p0QA1p0QG1p0QO1p0R71p0R>1p0RL1p0RN1p0S51p0S:1p0SC1p0SJ1p0T01p0T<1p0TG1p0TN1p0U51pR@U@1p_:UB1p]:UM1paDUE1p_LUH1p_HUJ1p`:V11p`BV11").
Proof.
intros regs pc mem model w addr len KB HF HE Hh Hlazy H17 Halloc H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HB.
pose proof (u64_range addr) as Har.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). alloc_top_bounds. unfold two_pow_64 in *. lia. }
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
assert (Hargs : mmap_fixed_args_ok ms).
{ unfold mmap_fixed_args_ok, ms.
rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
apply (srz_mmap_fixed_noaccess_at ms model (getr regs 17) addr len KB Hh Hlazy eq_refl
ltac:(rewrite H17; apply u64_lit; lia) Hargs Halloc
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc).
unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.
Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.
Lemma one_tid_ok : ltac2:(TCodec.tc2 tcn__RefNodes "='G&V<z&XEyR0&XA+1%2231%5241%8271&T;%:231%<231").
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.
Lemma node_set_tid : ltac2:(TCodec.tc2 tcn__RefNodes "RA'QL'RD'XByR0%211'H'A%113&S5r2%211(3%118%83631'='C%12<<%311&S7r3%211(@%116%B3631&QNr5%211(6%12H9%H3F31'Q4&XEr4%22N1+S0%N3521&S6r6%211%Q23Q01K&V1vX>vX=(R7r8r7%3221&UI'RM%L11q031&R2&R0r9&Q1'G&V<zr1%L2QH1%4231&T;%6231%8231qa@QL1%;3QM17%>2=1%@11&T6%124I%K231q^LH1%Q06ONJIF1p0Q21p0Q71p0Q>1p0QE1p0R01paJR:1p_LR>1p_NR@1").
Proof.
intros ms model x8 Hh Hlazy Hsvc Hno Htid.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
match eff with
| mkEffectU ret [] [] [] [] [] =>
if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
then CheckOk (with_tid ret model) [] else CheckReject
| _ => CheckReject end).
{ intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
assert (Enx : forall i : tid_I,
mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
= mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
{ intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
assert (Hnode : node_ok segs scfg (mkCfg ms model) tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model))).
{ apply (node_chk segs scfg ms model x8 tid_I effs (fun i => with_tid (proj1_sig i) model) Hh Hsvc).
- intros [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
- intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
- intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
- intros i. rewrite with_tid_halted. exact Hh.
- intros i. rewrite with_tid_lazy. exact Hlazy.
- intros i. apply not_spurious_on. apply injected_family_off_none. rewrite in_sysno_sys_input, Hno. exact injected_arm_96. }
destruct Hnode as [Hfw Hbw]. split.
- intros i. rewrite Enx. apply Hfw.
- intros e st Hss. destruct (Hbw e st Hss) as (i & -> & ->). exists i. rewrite Enx. split; reflexivity.
Qed.
Lemma srz_set_tid_at : ltac2:(TCodec.tc2 tcn__RefNodes "RA'QL'RD'XByR0%211&V0'H'A%114&S5r3%211(3%119%83631'='C%12==%311&S7r4%211(@%116%B3631&QNr6%211(6%12I9%H3F31'Q4&XEr5%22O1+S0%N3521&S6r7%211%Q23Q01K'G&V<zr1%=2Q:1%4231&T;%6231%8231'V5vX>vX=(R7&R2&R0r;r2%3221%511&T6r:%2251%:241r8%?4>=21p0A1paBQO1r9%@281%D4CB1Q0p041p0Q01p0Q51p0Q<1p0QC1p0QN1pR<R81paJR:1p_LR>1p_NR@1").
Proof.
intros ms model x8 K Hh Hlazy Hsvc Hno Htid Hk.
apply (srz_cases1 segs scfg (mkCfg ms model) _ _ K (exist _ (Z_to_bv 64 1) one_tid_ok)
(node_set_tid ms model x8 Hh Hlazy Hsvc Hno Htid)).
intros [t Ht]. cbn [proj1_sig]. apply Hk. exact Ht.
Qed.
Lemma rz_set_tid : ltac2:(TCodec.tc2 tcn__RefNodes "SA&THy5'XByR0%211%5241'Ay8%611%311p061'RD&V0yQ0%<11'H%:12&QJvX>r6%3221(6r1%2291%93841'9&QKr2%211(E%?3521%I1K&S5r5%211(3%11Q0%F3631'='C%12Q4Q4%311&S7%11H(@%115%O3531&U6r;(X@+A(F%33QC21%6251&XA+S0%22QE1%Q:3QE41&S6r8%211%Q>3N1I'G&V<z&XE%12QOQ<%4231&T;%6231%8231'V5vX=(R7&U7vW9&U9r?+:%N3R>1L%4331QE&U;r>+4%3221r=r<%=5<7321&T6%12QNQ9%A231r:%E4R:D21p0G1paBRJ1%E5D=:9Q?%G215r9%K4R@J21p051p0Q71p0Q<1p0QH1p0R21p0R:1p0RA1paDRL1pR<RO1p_LS11p`HS31p_HS41p`:S;1p`BS;1").
Proof.
intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hk.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply (srz_set_tid_at _ model (getr regs 17));
[exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid |].
intros t Ht. rewrite adv_set_epend. apply Hk. exact Ht.
Qed.
Lemma rz_exit_at : ltac2:(TCodec.tc2 tcn__RefNodes "S4&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'H%912&QJvX>r6%3221(6r2%2291%93841'9&QKr3%211(E%?3521%H1J&S5r5%211(3%11O%F3631'='C%12Q3Q3%311&S7%11H(@%115%O3531'L&U6r;(X@+A(F%33QC21%6251&XA+RN%22QE1%Q;3QE41+RM%52QH1%Q>3QH71%?241r<+:%?3QO1=%B231%QD3QN1Q@'V5vX=(R7&U7vW9r=r:%4532<J1r9%7221&V4&XDr7+WO%K2R>1%43R?31&S4%119%8231%C4R5B:1p0E1p0K1p0Q<1p0QF1p0QN1p0R51p]JRI1paDRA1p_LRD1p`HRF1p_HRG1p`:RN1p`BRN1").
Proof.
intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.
Lemma rz_exit_at_lit : ltac2:(TCodec.tc2 tcn__RefNodes "S=&THy5'XByR0%211%5241'Ay8%611%311p061'RDyQ0%;11'Q4'H%:13&QJvX>r6%3221(6r2%22:1%93841'9&QKr3%211(E%?3521%I1K&S5r5%211(3%11Q0%F3631'='C%12Q4Q4%311&S7%11H(@%115%O3531'L&U6r;(X@+A(F%33QD21%6251&XA+RN%22QF1%Q;3QF41+RM%52QI1%Q>3QI71%?241r<+:%?3R01=%B231%<2R0Q@%QE3R021'G&V;zr7%3221&V<+X0%2241%8241'V5vX=(R7&U7vW9r>r=%45321FQ4r:%7221&V4r8%Q32RG1&S4%116%5231%@4R<?71p0B1p0L1p0Q31p0QD1p0QN1p0R61p0R=1p]JRH1paDRJ1p_LRM1p`HRO1p_HS01p`:S71p`BS71").
Proof.
intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10 Hc.
rewrite <- (bv_and_255_small code Hc). eapply rz_exit_at; eassumption.
Qed.
Lemma vm_backing_used_simple : ltac2:(TCodec.tc2 tcn__RefNodes "Q1'RD'H'='C'XByR0%211%4211%611&S7r1%211(@%116%=3631%=19&S8r2%211%71=%C3521'Q4&SJr3%211&SI&S9%114%311%L3851p0:1p0A1p_@Q01").
Proof.
intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.
Lemma vm_backed_bytes_no_noaccess : ltac2:(TCodec.tc2 tcn__RefNodes "H'RG'H'='C'XByR0%211%4211%611&T2r1%211(@%116%=3631'Q4&SIr2%211&SO%113%D3631p081p^FG1").
Proof. intros h H. unfold vm_backed_bytes, vm_backed_maps. rewrite H. reflexivity. Qed.
Lemma brk_grow_ok_aligned_intro : ltac2:(TCodec.tc2 tcn__RefNodes "R@'RD'Q4'RG&S9r2%211'XByR0%211&SKr1%211'H&V=&XE%1285&SB%4221z%73B21r4%8215%:3E14&V<r5%2271%<2C6%4291&V;&V:%@2G6r7%3221&RJr6%211%8241'9&SE&8'C%12Q1Q1&T3%11<&T0%11>%73531&XAr8%D21Q1%32Q;1%=35A1(E%Q93@21&SJr:%211r9%M221&SN%11<%Q1231&T<r;%QB2QI@%Q421:%C2QK1%53411%QH3O1@p081p0A1p0Q31p0Q=1p0Q@1p0QD1p0QH1t]<R4R11t^FR;R81p^0R=1p_@R?1").
Proof.
intros m d h b Hbal Hdal Hd Hb0 Htop Hrf Hlive.
pose proof (u64_range b) as Hbr.
assert (Htb : (alloc_top h < 2 ^ 64)%Z) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _)) by lia.
rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.
Lemma brk_grow_admissible_init : ltac2:(TCodec.tc2 tcn__RefNodes "RJ'='C'XByR0%211%4211%611'Q4'RD&V;&SFr7%211&XEr6%22<1%7241'H&V=%62@8&SB%3221z%63@21r3%7215%93C14&V<r4%2271r:%B2L1%52:1&V:r;%F2Q01%321F&RJ(S@r<(@%11Q4r8r9%68533::2>1%811%Q52:1%Q62Q44'RG&S9%117r>r=%?82<<11G>C%Q53641&S7%11J%Q83QC1@%QJ1QF&S8%11J%E1QI%Q=3421'9&T<&XAr@%QF2R01%Q321Q2%42R21%63O11(E%QG3921p0;1p0A1p0E1p0M1p0O1p0Q>1p0QB1p0QF1p0QJ1p0R21p^0R<1p_LR<1p_<R>1pa0RB1p_FRC1p]@RD1p`FRC1").
Proof.
intros reserved brk0 mbase sp lim model d Htop Hbal Hdal Hd Hb0 Hce Hlim Hvm Hlz Hmt.
pose proof (brk_grow_ok_aligned_intro model d) as H. cbv zeta in H. rewrite Hvm in H. cbn -[alloc_top Z_to_bv bv_unsigned Z.add Z.modulo region_free] in H.
apply H; try assumption; try lia.
- rewrite app_nil_r. apply region_free_above_top. exact Htop.
- rewrite vm_backing_used_simple by assumption. rewrite Hvm. cbn. lia.
Qed.
End WithSegs.
End FPX_1.
Section FPX_2. Context {fx : PropExec.FPState}.
Local Open Scope Z_scope.
Lemma u64_roundtrip : ltac2:(TCodec.tc2 tcn__RefNodes ";'XByR0%211'H&XA&XEr1%2261%4271%63713paH81").
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma region_free_app : ltac2:(TCodec.tc2 tcn__RefNodes "J'='C'XByR0%211%4211%611'H'9&SE&8r4r3%33821r2r1%73321&7%93743%:3754%3221%>3=51p`2B1p_>C1p_8B1p_6C1").
Proof.
induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.
Lemma region_free_In : ltac2:(TCodec.tc2 tcn__RefNodes "Q:'='C'XByR0%211%4211%611'H'9&SEr5r4r3%43321(E%83721&V7(Br2%24??71r6%53@21'L&V;&V:&XE%12G6%22HA%4221%42JB%7221%62LC%8231%:217%<241p0>1p0E1p`JQ11p]<Q21p`2Q31p_>Q41p_4Q31").
Proof.
induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
apply region_free_cons in Hrf as [Hd Hrf].
destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.
Lemma region_free_intro : ltac2:(TCodec.tc2 tcn__RefNodes "Q:'='C'XByR0%211%4211%611&V7(Br2r1%347721r5%63821'L&V;&V:&XE%12?6r4%32A1%5231r3%62D1%9231%82F@%:231%<219%>241p0@1p`JJ1p]<K1'H'9&SE%13@=J(E%53421p071p`2Q31p_>Q41p_4Q31").
Proof.
induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.
Lemma map_has_head : ltac2:(TCodec.tc2 tcn__RefNodes "G'XByR0%211'='C%1233%311'H'9&S;(:(Br3r2%34<<21r1%63;21%83154(E%<3;21p_4>1p`2C1p]8D1").
Proof. intros. unfold map_has. cbn [existsb fst snd]. rewrite !bv_eqb_refl. reflexivity. Qed.
Lemma map_has_cons : ltac2:(TCodec.tc2 tcn__RefNodes "K'C'XByR0%211%4211'=%112'H'9&S;r1r3r2%43321(E%83721(:r5%23>16r4%;3219%>3=17p071p_4A1p`2E1p]8F1p`8F1").
Proof. intros p a n l H. unfold map_has in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.
Lemma map_contains_head : ltac2:(TCodec.tc2 tcn__RefNodes "Q8'XByR0%211'='C%1233%311&V;&XEr5%2291r3%42;1%6231&V:r4%82?1%3215r6%;2B1%621:%>241'H'9&S:(:(Br7%24JJ1:%43H1B%631E?(E%:3921p0<1p0E1p_4M1p`2Q21p_>Q31pa>Q41p]8Q51").
Proof.
intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.
Lemma map_contains_cons : ltac2:(TCodec.tc2 tcn__RefNodes "K'C'XByR0%211%4211'=%112'H'9&S:r1r3r2%43321(E%83721(:r5%23>16r4%;3219%>3=17p071p_4A1p`2E1p_>F1p`8F1").
Proof. intros p lo n l H. unfold map_contains in *. cbn [existsb]. rewrite H. apply orb_true_r. Qed.
Lemma map_remove_nil : ltac2:(TCodec.tc2 tcn__RefNodes "?'XByR0%211'H'='C%1244%311&S<(@%114r1%4221%:3613p]8<1").
Proof. reflexivity. Qed.
Lemma map_remove_head : ltac2:(TCodec.tc2 tcn__RefNodes "F'XByR0%211'='C%1233%311'H&S<(:(Br3r2%34;;21r1%63:21%8215%9236%;3<21p_4=1p`2B1p]8C1").
Proof. intros. unfold map_remove. cbn [List.filter fst]. rewrite bv_eqb_refl. reflexivity. Qed.
Lemma map_remove_skip : ltac2:(TCodec.tc2 tcn__RefNodes "M'XByR0%211'='C%1233%311&K'Hr4r2%33921%511&S<(:(Br5%24??18%43=18r3%7221%82;2%83A51%?3A31p0<1p_4C1p]8H1p`JI1p]<J1").
Proof. intros b s a l H. unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq _ _ H). reflexivity. Qed.
Lemma map_remove_notin : ltac2:(TCodec.tc2 tcn__RefNodes "L'='C'XByR0%211%4211%611&V7(Br2r1%347721r4%63821&K'Hr3%23=15%411p061p`J@1p]<A1&S<%127>%93B18p041p]8F1p_4E1").
Proof.
induction l as [|[b s] l IH]; intros a H; [reflexivity|].
rewrite map_remove_skip by (apply (H b s); left; reflexivity).
rewrite IH by (intros b' s' Hin; apply (H b' s'); right; exact Hin). reflexivity.
Qed.
Lemma disjoint_base_ne : ltac2:(TCodec.tc2 tcn__RefNodes "Q6'XByR0%211&V<z&XEr3%2261%5241r2%5291%8271'L&V;&V:r6%;2?1r5%=2A1%5231r4%@2D1%9231%922@%;218%=231&K'Hr7%23K<1%411p061p0E1p0I1p`JQ01p]<Q11p`2Q21p_>Q31").
Proof. intros lo n b s Hn Hs Hd ->. lia. Qed.
Lemma live_bytes_cons : ltac2:(TCodec.tc2 tcn__RefNodes "K'XByR0%211'='C%1233%311'H'Q4&S2(:(Br3r2%34<<21r1%63;21%811&V:&XE%12C7%<16%4221%@3?61p_4B1p`2G1p]8H1").
Proof. reflexivity. Qed.
Lemma live_bytes_app : ltac2:(TCodec.tc2 tcn__RefNodes "F'='C'XByR0%211%4211%611'H'Q4&S2&8r2r1%33821%511&V:%715%815%3221%<3;51p_8>1p_6?1").
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.
Lemma live_bytes_nonneg : ltac2:(TCodec.tc2 tcn__RefNodes ">'='C'XByR0%211%4211%611&V;z&S2r1%211%5241p_471").
Proof. induction l as [|[a n] l IH]; [cbn; lia|]. cbn [live_bytes]. pose proof (u64_range n). lia. Qed.
Lemma live_bytes_map_remove_le : ltac2:(TCodec.tc2 tcn__RefNodes "B'='C'XByR0%211%4211%611&V;&S2&S<r2r1%3221%511%614%8221p]8<1p_4;1").
Proof.
induction l as [|[b s] l IH]; intros a; [cbn; lia|].
unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [live_bytes];
fold (map_remove l a); pose proof (IH a); pose proof (u64_range s); lia.
Qed.
Lemma maps_subtract_nil : ltac2:(TCodec.tc2 tcn__RefNodes "B'Q4'H'='C'XByR0%211%4211%611&S=(@%114r2r1%53321%>3714p^H@1p_>A1").
Proof. reflexivity. Qed.
Lemma maps_subtract_cons : ltac2:(TCodec.tc2 tcn__RefNodes "O'XByR0%211'Q4'='C%1244%311'H&S=(:(Br5r4%34<<21r1%63:21r3r2%:3321&8&S1%14:954%>3865%43B21%A3B61p_4C1p^HH1p_>I1pa>K1p]8L1").
Proof. reflexivity. Qed.
Lemma maps_subtract_app : ltac2:(TCodec.tc2 tcn__RefNodes "I'='C'XByR0%211%4211%611'Q4'H&S=&8r4r3%33821r2r1%73321%83632%93643%93>21%<3>41p^H>1p_>?1p_8A1p_6B1").
Proof.
induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.
Lemma iv_subtract_covered : ltac2:(TCodec.tc2 tcn__RefNodes "Q1'XByR0%211'Q4&V;r2&XEr4%2271%5241&V:r5%62;1%3215%:219'H'='C%12@@%311&S1r6r3%342<@1(@%117%;3731p0=1p0C1p^HJ1p_>K1pa>M1p]8N1").
Proof.
intros a sz lo hi H1 H2. unfold iv_subtract.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.
Lemma iv_subtract_self : ltac2:(TCodec.tc2 tcn__RefNodes "F'XByR0%211'H'='C%1244%311&S1r2r1&XE%12;3&V:%32=4%2231%847641(@%11<%@3<31pa>B1p]8C1").
Proof. intros a sz. apply iv_subtract_covered; lia. Qed.
Lemma iv_subtract_disjoint : ltac2:(TCodec.tc2 tcn__RefNodes "Q>'XByR0%211'Q4&V<z&XEr3%2271%5241&V;r2%2251'Lr6%92>1%6291&V:r5%=2B1%3251r4%<221%:271'H'='C%12II%311&S1r7%241A=:(:(B%14Q0Q04D(@%119%53:31%>3:71p0@1p0L1p0Q01p^HQ71p_>Q81pa>Q:1p]8Q;1").
Proof.
intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
destruct Hd as [Hd | Hd].
- rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
rewrite Z.max_l by lia. rewrite u64_roundtrip.
replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite u64_roundtrip. reflexivity.
- rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.
Lemma iv_subtract_suffix : ltac2:(TCodec.tc2 tcn__RefNodes "Q@'XByR0%211'Q4&V<&XEr4%2261r2%5221&V;r3&V:r5%92=1%3218%6251r6%=2A1%7215%:219'H'='C%12FF%311&S1r7%241;?F(:(B&XA&VA%L2Q06%22E1%42Q21%64Q2Q291(@%11>%:3?31%C3?<1p0E1p0J1p0Q21p^HQ91p_>Q:1pa>Q<1p]8Q=1").
Proof.
intros a sz lo hi H1 H2 H3. unfold iv_subtract.
rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_ge _ _) H3). cbn [app].
rewrite Z.min_r by lia. reflexivity.
Qed.
Lemma iv_subtract_prefix : ltac2:(TCodec.tc2 tcn__RefNodes "QA'XByR0%211'Q4&V;r2&XEr4%2271%5241r5%52:1%8217&V<r3&V:r6%;2@1%3217%6251'H'='C%12EE%311&S1r7%241;AD(:(B&XA%12NH&VA%K2Q07%C21A%321L%62Q31%84Q3Q361(@%11@%<3A31%E3A>1p0G1p0O1p0Q31p^HQ:1p_>Q;1pa>Q=1p]8Q>1").
Proof.
intros a sz lo hi H1 H2 H3. unfold iv_subtract.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
rewrite Z.max_r by lia. reflexivity.
Qed.
Lemma iv_subtract_sizes : ltac2:(TCodec.tc2 tcn__RefNodes "Q9'XByR0%211'Q4&V;zr3%3221&V<&V@+2+R0%3221%5271&XEr6%22?1%=21;'Q3'C%12BB&Dr1%23EE1%:2G1r5%F221q`871&S1r8r7%3421@6%>3<51p0@1p0E1p0L1pYDQ11p^HQ21p_>Q31pa>Q51p]8Q61").
Proof.
intros a sz lo hi N Hlo Hhi Hs. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract. apply Forall_app. split.
- destruct (bv_unsigned a <? lo) eqn:E; [|constructor].
apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|constructor].
apply Z.ltb_lt in E. constructor; [|constructor]. cbn [snd].
rewrite u64_lit by lia. lia.
Qed.
Lemma maps_subtract_sizes : ltac2:(TCodec.tc2 tcn__RefNodes "Q;'='C'XByR0%211%4211%611'Q4&V;zr3%3221&V<&V@+2+R0%3221%5271'Q3&XE&Dr1%23BB1%42D1r4%A221q`8E1r6%:3G21r5%F271q`8J1&S=r7%23175%A3N41p081p0D1p0K1pYDQ01p^HQ11p_>Q21p_4Q41").
Proof.
induction l as [|[a sz] l IH]; intros lo hi N Hlo Hhi H; [constructor|].
inversion H as [|p l' Hp Hl]; subst. cbn [maps_subtract]. apply Forall_app. split.
- apply iv_subtract_sizes; assumption.
- apply IH; assumption.
Qed.
Lemma map_remove_sizes : ltac2:(TCodec.tc2 tcn__RefNodes "N'='C'XByR0%211%4211%611'Q4'Q3&V;&XE&Dr1%23991%42;1r2%7221q`8<1r3%;3>21%;262q`8@1&S<r4%2216%A3D41p071pYDD1p]8H1p_4G1").
Proof.
intros l a N H. unfold map_remove. apply List.incl_Forall with (l1 := l); [|exact H].
apply List.incl_filter.
Qed.
Lemma maps_subtract_length : ltac2:(TCodec.tc2 tcn__RefNodes "H'='C'XByR0%211%4211%611'Q4'O&<&S=r3r2r1%43321%62:1&Mu2%92=7%3221%<251p^H>1p_>?1p_4A1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi; [cbn; lia|].
cbn [maps_subtract]. rewrite length_app. cbn [length].
assert (length (iv_subtract a sz lo hi) <= 2)%nat.
{ unfold iv_subtract. rewrite length_app.
destruct (_ <? _); destruct (_ <? _); cbn; lia. }
specialize (IH lo hi). lia.
Qed.
Lemma map_remove_length : ltac2:(TCodec.tc2 tcn__RefNodes "B'='C'XByR0%211%4211%611'O&<&S<r2r1%3221%5281%6294%8221p]8<1p_4;1").
Proof.
induction l as [|[b s] l IH]; intros a; [cbn; lia|].
unfold map_remove. cbn [List.filter fst]. destruct (negb (bv_eqb b a)); cbn [length];
fold (map_remove l a); specialize (IH a); lia.
Qed.
Lemma live_bytes_iv_subtract_le : ltac2:(TCodec.tc2 tcn__RefNodes "G'XByR0%211'Q4&V;r2r1%3221&S2&S1r5r4r3%443218%611&XE%12?5%=231p0;1p^H@1p_>A1pa>C1p]8D1").
Proof.
intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
unfold iv_subtract.
destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
cbn [app live_bytes];
first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
rewrite ?u64_lit by lia; lia.
Qed.
Lemma live_bytes_maps_subtract_le : ltac2:(TCodec.tc2 tcn__RefNodes "H'='C'XByR0%211%4211%611'Q4&V;r2r1%3221&S2&S=r4r3%33217%511%614%;221p091p^H>1p_>?1p_4A1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.
Lemma maps_subtract_all_nil : ltac2:(TCodec.tc2 tcn__RefNodes "?'='C'XByR0%211%4211%611'H&S>r1(@%116%4231%63714p_D81").
Proof. reflexivity. Qed.
Lemma maps_subtract_all_cons : ltac2:(TCodec.tc2 tcn__RefNodes "O'='C'XByR0%211%4211%611'H&S>r4(:(Br3r2%34::21r1%63;21%9281&S=&XE%12A8&V:%32C9%2231%63?41%A21:%C3D91p]NE1p`2H1p]8I1p_DH1").
Proof. reflexivity. Qed.
Lemma live_bytes_maps_subtract_all_le : ltac2:(TCodec.tc2 tcn__RefNodes "B'='C'XByR0%211%4211%611&V;&S2&S>r1r2%3221%511%614%8221p_D:1p]N;1").
Proof.
induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.
Lemma vm_backed_bytes_le_live : ltac2:(TCodec.tc2 tcn__RefNodes "9'RG&V;&SIr1%211&SO%113%6231p^F81").
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.
Lemma vm_backing_used_le_live : ltac2:(TCodec.tc2 tcn__RefNodes "Q1'RD'H'='C'XByR0%211%4211%611&S7r1%211(@%116%=3631%=19&S8r2%211%71=%C3521&V;&SJr3%211&SO&S9%114%311%8251p0:1p0A1p_@Q01").
Proof.
intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.
Lemma grant_budget_intro : ltac2:(TCodec.tc2 tcn__RefNodes "Q='RD'Q4'H'='C'XByR0%211%4211%611&S7r2%211(@%116%=3631%=19&S8r3%211%71=%C3521&V;&V:&SO&S9r4%211%411%621;&SN%114%:231&SJr5%211%=21:%<13%811%A231p081p0D1p0K1p`2Q:1p_@Q<1").
Proof. intros m n Hl Hm H. pose proof (vm_backing_used_le_live m Hl Hm). lia. Qed.
Lemma mprotect_budget_ok_intro : ltac2:(TCodec.tc2 tcn__RefNodes "Q:'RD'XByR0%211'H'='C%1244%311&S7r3%211(@%116%:3631%:1<&S8r4%211%71@%@3521&V;&SO&S9r5%211%411&SN%113%8231'9&T@r6%2319@(E%O3521p071p0A1p0H1p`2Q41p]:Q51p_@Q91").
Proof.
intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
rewrite mprotect_model_next_eq. apply Z.leb_le.
etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.
Lemma file_read_length_eq : ltac2:(TCodec.tc2 tcn__RefNodes "L'='XBy8%211%411yR0%511'H'>&<&QGr3r2r1%43321%62<1&V6&Q9%115&N%;2A9%419%3221%7251%A3@91p]LC1p`6D1p^2G1").
Proof. intros. rewrite length_file_read. reflexivity. Qed.
Lemma file_read_length_le : ltac2:(TCodec.tc2 tcn__RefNodes "L'='XBy8%211%411yR0%511'G'O&<&QGr3r2r1%43321%62<1&Q9%114%:231&N%;2A9%519%3221%?281%A261p]LC1p`6D1p^2G1").
Proof. intros data off count. rewrite file_read_length_eq. split; lia. Qed.
Definition cand (base N : Z) (j : nat) : Z := base + Z.of_nat j * (2 * N).
Definition zconflict (a n : Z) (p : word * word) : Prop :=
a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.
Definition zconflictb (a n : Z) (p : word * word) : bool :=
(a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).
Lemma zconflictb_spec : ltac2:(TCodec.tc2 tcn__RefNodes "F'Q4'C'XByR0%211%4211&J'H'9&UMr3r2r1%43321(E%83721&UL%13765%<231p`8>1p`2D1p]8E1").
Proof.
intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.
Lemma cand_spacing : ltac2:(TCodec.tc2 tcn__RefNodes "K'Q4'>&V;zr3%3221&Q0r2%2241&V:&UKr6r5r4%43321&V>+2%2215%9241%9387?%B221p0=1p0A1p_2F1p^NG1pYDI1p]>J1").
Proof. intros base N j k HN H. unfold cand. nia. Qed.
Lemma conflict_unique : ltac2:(TCodec.tc2 tcn__RefNodes "Q:'Q4'C'XByR0%211%4211'>'G&V;zr4%3221r5%5231%7231&XE&D%13==7%32?1r6%<221&UL&UKr8r7%3321?%5317>r9%6315B%8315:'H%13I<Cp031p071p0>1p0E1p_2N1p^NO1p`8Q11p`2Q71pYDQ81p]>Q91").
Proof.
intros base N n p j k Hn Hs [A1 A2] [B1 B2].
destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
- pose proof (cand_spacing base N j k ltac:(lia) Hlt). lia.
- pose proof (cand_spacing base N k j ltac:(lia) Hgt). lia.
Qed.
Lemma filter_keep_all_but_one : ltac2:(TCodec.tc2 tcn__RefNodes "Q@'>'9p021'=%114'V8r1%2271&V7r2r4%33;21r5%53=41'Hr7%116(E%43A21r8%11:%73D14r6%93G1;p031p071p0=1p0@1p_2L1p^NM1'O&<r3%22Q11(5&V9&?%I1O%211q^NQ71%53Q818%:2Q91%811%=2:1p0?1p0Q61p_0Q:1pYFQ=1").
Proof.
intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
inversion Hnd as [|x l Hnotin Hnd']; subst.
cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
-
assert (Hall : forall k, In k js -> P k = false).
{ intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
subst k. exact (Hnotin Hk). }
assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
{ clear -Hall. induction js as [|k js IH]; [reflexivity|].
cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
intros k' Hk'. apply Hall. right. exact Hk'. }
rewrite Hid. lia.
- cbn [List.length].
assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
{ apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
lia.
Qed.
Lemma pick_candidate : ltac2:(TCodec.tc2 tcn__RefNodes "R1'Q4'='C'XByR0%211%4211%611'>%811'G&V;zr3%3221r4%5231%7231'Q3&XE&Dr1%23AA1%42C1r6%>221q`8D1%93E1>'V8%12E@&Q0&<r5%22K1%32JC%5221'I&V7%13NA>r8%33Q2C1&K&UL&UKr<r;%3321Q1r:r2%73321%911p0;1p`8Q>1%Q;2?1q^NQ>1%C2Q?1p0E1p0L1p0O1p0Q:1p_0QC1p_4QF1p`2QN1pYDQO1p]>R01").
Proof.
intros base N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
- destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
- inversion Hsz as [|p' l' Hp Hl]; subst.
set (js' := List.filter (fun j => negb (zconflictb (cand base N j) n p)) js).
assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
assert (Hlen' : (length js <= S (length js'))%nat).
{ apply filter_keep_all_but_one; [exact Hnd|].
intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
eapply (conflict_unique base N n p); eassumption. }
destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
intros q [<- | Hq].
+ intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
+ apply Hfree. exact Hq.
Qed.
Lemma region_free_of_noconflict : ltac2:(TCodec.tc2 tcn__RefNodes "QB'='C'XByR0%211%4211%611'Q4&V;zr2%3221&V<&V:r4r3%3221&V@+2+R0%3221%9251&V7r1r7%33D21&K&ULr6%2351C%411p061p`8K1'H'9&SE&XA%12Q29r5%32Q41%53@31(E%93821p0;1p0G1p0Q21p0Q31p`2Q81p]8Q91p_4Q;1").
Proof.
induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
rewrite !u64_lit by lia.
specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
- right. apply Z.ltb_ge. lia.
- left. apply Z.ltb_ge. lia.
Qed.
Lemma grant_exists_na_gen : ltac2:(TCodec.tc2 tcn__RefNodes "RL'XByR0%211'RD'Q4&V<zr4%3221'H&V=r5&SB%3221%53:18'G&V;%12;6r6%3281%5231'Q3'C%12EE&XE&Dr1%23II1%42K1r8%>221q`881&8&T3&S9%116%311&T0%113%73@31%C3A91&V?&<r9%:11%<11%912%?3H21%62I1%811%Q221Q0%Q92Q1Q7%Q;3Q@1Q>r7%QA2Q@1&V:&V>+2r;%3221%42A1%62Q01%7214&RJr<%O11%311%QC251'I'9&UNr?r>%3421Q?9(E%R23621q]8R:1%92R;1p0;1p0I1p0L1p0O1p0Q:1p0QO1p0R61p0R=1p]>RB1p6RC1p`2RD1pYDRE1p_@RG1p^JRI1").
Proof.
intros hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband.
set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
destruct (pick_candidate base N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
as (j & Hj & Hfree).
apply in_seq in Hj.
exists (Z_to_bv 64 (cand base N j)).
pose proof (alloc_top_lt (m_vmmaps m)) as Htl. unfold two_pow_64 in Htl.
assert (Hc : base <= cand base N j <= base + C * (2 * N)) by (unfold cand; nia).
assert (E1 : cand base N j mod page_size = 0).
{ unfold cand. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal, Hbal by lia.
rewrite Z.mul_0_r. reflexivity. }
generalize dependent (cand base N j). intros c Hfree Hc E1.
assert (G : 0 <= c < 2 ^ 64 /\ (0 <= n < 2 ^ 64 /\ (0 < c /\ (c + n <= alloc_top (m_vmmaps m) /\ c + n < 2 ^ 64)))).
{ clear Hfree Hsz E1 HNal Hbal. generalize dependent (alloc_top (m_vmmaps m)). intros top Hband Htl. nia. }
destruct G as (G0 & G1 & G2 & G3 & G4).
unfold grant_ok_na. rewrite (u64_lit c G0).
rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _) G2), (proj2 (Z.leb_le _ _) G3).
fold l. rewrite (region_free_of_noconflict l c n (proj1 G0) (proj1 Hn) G4 Hfree).
reflexivity.
Qed.
Lemma grant_exists_gen : ltac2:(TCodec.tc2 tcn__RefNodes "S5'XByR0%211'RD'Q4&V<zr4%3221'H&V=r5&SB%3221%53:18'G&V;%12;6r6%3281%5231'Q3'C%12EE&XE&Dr1%23II1%42K1r8%>221q`881&8&T3&S9%116%311&T0%113%73@31%C3A91&V?&<r9%:11%<11%912%?3H21%62I1%811%Q221Q0%Q92Q1Q7%Q;3Q@1Q>r7%QA2Q@1&V:&V>+2r;%3221%42A1%62Q01%7214&RJr<%O11%311%QC251&SJr=%211%@21=&SN%Q714%211%QK241'I'9&U1r@r?%3421QG<(E%R:3621q]8RB1%92RC1p0;1p0D1p0Q21p0Q51p0Q81p0QC1p0R81p0R?1p0RF1p]>RK1p6RL1p`2RM1pYDRN1p_@S01p^JS21").
Proof.
intros hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband Hlive.
destruct (grant_exists_na_gen hint m N n C base HN HNal Hn Hsz Hcnt Hbal Hb0 Hband) as [a Ha].
exists a. unfold grant_ok. unfold grant_ok_na in Ha. rewrite Ha.
rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.
Lemma alloc_top_ge_window : ltac2:(TCodec.tc2 tcn__RefNodes "A'RG&V;&SG&XEyR0&SMr1%211%5241%8271+SoomohPPP0&RJr2%211%=241p061p^F@1").
Proof. intros h H. unfold alloc_top. rewrite stack_max_size_val. unfold sp_window_lo in H. lia. Qed.
Lemma grant_exists : ltac2:(TCodec.tc2 tcn__RefNodes "RB'XByR0%211'RD'Q4&V;&SG&XE&SM&S9r2%211%411%62<1%9281'Gz%<217&V@+2+N%3221%A2<1%8261'Q3'C%12HH&Dr1%23KK1%G2M1%J21:q`861&8&T3r4%K11%311&T0%113%73>31%A3?91&V?&<r5%Q411%<11%912%?3F21%62G1%811+QWR0%Q?221&V:&SJr6%211%421=&SN%QB14%211%QH241'I'H'9&U1r9r8r7%4432Q91(E%83721q]8R61%;2R71p0=1p0G1p0Q31p0QF1p0R01p`2R;1p_@R=1p^JR?1").
Proof.
intros hint m n Hsp Hn Hsz Hcnt Hlive.
pose proof (alloc_top_ge_window _ Hsp).
apply (grant_exists_gen hint m (2 ^ 30) n 40000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.
Lemma grant_exists_na : ltac2:(TCodec.tc2 tcn__RefNodes "R8'XByR0%211'RD'Q4&V;&SG&XE&SM&S9r2%211%411%62<1%9281'Gz%<217&V@+2+N%3221%A2<1%8261'Q3'C%12HH&Dr1%23KK1%G2M1%J21:q`861&8&T3r4%K11%311&T0%113%73>31%A3?91&V?&<r5%Q411%<11%912%?3F21%62G1%811+QWR0%Q?221'I'H'9&UNr8r7r6%4432Q01(E%83721q]8QM1%;2QN1p0=1p0I1p0Q<1p0QF1p`2R11p_@R31p^JR51").
Proof.
intros hint m n Hsp Hn Hsz Hcnt.
pose proof (alloc_top_ge_window _ Hsp).
apply (grant_exists_na_gen hint m (2 ^ 30) n 40000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.
Lemma grant_exists_big : ltac2:(TCodec.tc2 tcn__RefNodes "RB'XByR0%211'RD'Q4&V;&SG&XE&SM&S9r2%211%411%62<1%9281'Gz%<217&V@+2+Q3%3221%A2<1%8261'Q3'C%12HH&Dr1%23KK1%G2M1%J21:q`861&8&T3r4%K11%311&T0%113%73>31%A3?91&V?&<r5%Q411%<11%912%?3F21%62G1%811+o8%Q?221&V:&SJr6%211%421=&SN%QB14%211%QH241'I'H'9&U1r9r8r7%4432Q91(E%83721q]8R61%;2R71p0=1p0G1p0Q31p0QF1p0R01p`2R;1p_@R=1p^JR?1").
Proof.
intros hint m n Hsp Hn Hsz Hcnt Hlive.
pose proof (alloc_top_ge_window _ Hsp).
apply (grant_exists_gen hint m (2 ^ 35) n 1000 (2 ^ 32)); try assumption; try lia; reflexivity.
Qed.
Lemma grant_ok_over_budget : ltac2:(TCodec.tc2 tcn__RefNodes "O'XByR0%211'RD'Q4&V<&SN&S9r3%211%411&V:&SJ%115r1%4221%;261'H'9&U1r5r4r2%4432?1(;%83721p0:1p`2G1p]8J1p_@J1p^JL1").
Proof.
intros hint m a n H. unfold grant_ok.
destruct (bv_unsigned a mod page_size =? 0); [|reflexivity].
destruct (0 <? bv_unsigned a); [|reflexivity].
destruct (bv_unsigned a + n <=? alloc_top (m_vmmaps m)); [|reflexivity].
destruct (region_free _ a (Z_to_bv 64 n)); [|reflexivity].
rewrite (proj2 (Z.leb_gt _ _) H). reflexivity.
Qed.
End FPX_2.
