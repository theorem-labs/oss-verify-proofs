(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Mm.Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim PropExec CatSim CatExec WallSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AllocSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AllocSim.WithFP1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.WallSim."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1S"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1fst"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1snd"]; ["1true"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3Forall"; "4N"; "4Z"; "5equiv"; "5modeled"; "6omni_strong_equiv"; "7nat_to_word"; "8check_brk"]; ["9CheckOk"; "9check_result"; ":Fs"; ";PhdrInfo"; ";Segment"; ";mkImage"; "<Ok"; "<Unmodeled"; "<outcome"; "=cosafe"; "=exec"; "=exits_with"; "=omni_run"; ">Build_machine_state"; ">machine_state"; ">ms_gpr"]; [">ms_svc_pending"; "?SNext"; "?advance_past_svc"; "?apply_effect"; "?apply_zeros"; "?config"; "?init_config"; "?init_machine_state"; "?is_prefix"; "?mkCfg"; "?mkEntry"; "?obs_trace"; "?reaches_error"; "?run"; "?segments_reserved"; "?sstep"]; ["?star"; "?step_to"; "?sys_input"; "@syscall_spec"; "AEntryDraw"; "BFdEntry"; "BMemCopy"; "BModel"; "BProcInput"; "BSyscallEffect"; "BVmMaps"; "Balloc_top"; "Bbrk_aslr_max"; "Beff_ret"; "Bevent"; "Bin_arg"]; ["Bin_argv"; "Bin_envp"; "Bin_fs"; "Bin_hwcap"; "Bin_sysno"; "Bin_uid"; "Binit_model"; "Bm_fds"; "Bm_fs"; "Bm_halted"; "Bm_vm_lazy"; "Bm_vmmaps"; "BmkEffectU"; "BmkVmMapsFull"; "Bpage_round_up_Z"; "Bpage_size"]; ["Bregion_free"; "Breserved_top"; "Bsource_alloc_limit"; "Bstack_max_size"; "Btarget_alloc_limit"; "Bvm_backed_bytes"; "Bvm_brk"; "Bvm_init_sp"; "Bvm_limit"; "Bvm_maps"; "Bvm_mmap_base"; "Bvm_noaccess"; "Bvm_reserved"; "Bvm_start_brk"; "Bwith_vmmaps"; "Cbrk_grants"]; ["Cbrk_model_next"; "Cbrk_page_range"; "Cbrk_spec"; "Cbrk_unmaps"; "Cbrk_zeros"; "Cforget_vm_ranges"; "Dbvmap"; "ET1"; "ET2"; "Foutcome_trace"; "Foutcomes_post"; "Fto_outcomes"; "Ebrk_grow_ok"; "Ebrk_model"; "Ebrk_r_ok"; "Ebrk_resolution_ok"]; ["Eoutcome_trace"; "Eoutcomes_post"; "Eto_outcomes"; "Ezmem"; "Gbufs_modeled"; "Gfd1chan"; "Gmsteps"; "Hfp_csr"; "Hfp_regs"; "Hmkst"; "Hrdn"; "Hregupd"; "Hv_addi"; "Ito_wallexit"; "Jadd"; "Jdiv"]; ["Jle"; "Jleb"; "Jlt"; "Jmodulo"; "Jmul"; "Jof_nat"; "Jpow"; "Jsub"; "0T'"; "0U"; "0V"; "0a"; "0abrk"; "0alim"; "0amb"; "0apc"]; ["0aph"; "0arnd"; "0asp"; "0b"; "0big"; "0brk0"; "0bufs"; "0c"; "0ceil"; "0code"; "0code'"; "0eff"; "0evs"; "0fx"; "0g"; "0h"]; ["0inp"; "0k"; "0l"; "0lim"; "0lo"; "0m"; "0m'"; "0maps"; "0mb"; "0mem"; "0model"; "0model'"; "0ms"; "0ms'"; "0n"; "0noaccess"]; ["0o"; "0old"; "0p"; "0pc"; "0ph"; "0r"; "0r2"; "0ranges"; "0rbrk"; "0regs"; "0req"; "0res"; "0reserved"; "0rlim"; "0rmb"; "0rnd"]; ["0rom"; "0rpc"; "0rph"; "0rrnd"; "0rsp"; "0s"; "0segs"; "0small"; "0source_segs"; "0sp"; "0st"; "KBV"; "KZ_to_bv"; "Kbv"; "Kbv_add"; "Kbv_sub"]; ["Kbv_unsigned"; "0t"; "0target_segs"; "0top"; "0tr"; "0w"; "0want"; "0x"; "0x8"; "0z"; "0zs"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma u_add_small : ltac2:(TCodec.tc2 tcn__AllocSim "L'VMyR0%211&TB&T>&W0r2%2261r1%4281%6231&TF+2+R0%3221%<251'C'J&VNr3%23C1>%@2D1%A2E3%C21@%83731p0:1pZ8H1pYHI1").
Proof.
intros a b H. rewrite bv_add_unsigned, bv_wrap64_mod. apply Z.mod_small.
pose proof (u64_range a). pose proof (u64_range b). lia.
Qed.
Lemma word_add_0_r : ltac2:(TCodec.tc2 tcn__AllocSim "<'VMyR0%211'C&VNr1&VLz%2271%53841%73815pYH91").
Proof.
intro a. apply bv_eq.
rewrite bv_add_unsigned.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
rewrite Z.add_0_r, bv_wrap64_mod. apply Z.mod_small. apply u64_range.
Qed.
Lemma word_add_sub_cancel : ltac2:(TCodec.tc2 tcn__AllocSim "='VMyR0%211'C&VO&VNr2r1%33721%53813%73813p^491p\<:1").
Proof.
intros r t. apply bv_eq.
rewrite bv_sub_unsigned, bv_add_unsigned, !bv_wrap64_mod.
rewrite Zminus_mod_idemp_l.
replace (bv_unsigned r + bv_unsigned t - bv_unsigned r)%Z
with (bv_unsigned t) by lia.
apply Z.mod_small. apply u64_range.
Qed.
Lemma word_neq0_unsigned : ltac2:(TCodec.tc2 tcn__AllocSim "C'VMyR0%211&F'Cr1&VLz%2271%53741%711'J&W0r2%22=1%;3418%=11p071p\<@1").
Proof.
intros r Hne Hu. apply Hne. apply bv_eq. rewrite Hu. reflexivity.
Qed.
Lemma word_add_nat_S : ltac2:(TCodec.tc2 tcn__AllocSim "G'VMyR0%211':'C&VNr2(VK+1(A%33921%63:51&Nr1%211%:3>41(2%114%611%>3B=1%@3B51p[4B1pYHD1").
Proof.
intros a k. apply bv_eq. unfold nat_to_word.
rewrite !bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (bv_unsigned (1 : word)) with 1%Z.
rewrite Zplus_mod_idemp_l, !Zplus_mod_idemp_r.
f_equal. lia.
Qed.
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
&& Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
then Some (Z_to_bv 8 0) else mem a.
Lemma apply_zeros_nil : ltac2:(TCodec.tc2 tcn__AllocSim "B'VMyR0%211'<y8%511%311p051'C&QDr1(;'>%12;;%311%6251%83916p[D:1").
Proof. reflexivity. Qed.
Lemma apply_zeros_one : ltac2:(TCodec.tc2 tcn__AllocSim "L'VMyR0%211'<y8%511%311p051'C&QDr3(7'>%12;;(=r2r1%34??21(;%116%93731%<2;1&T3%13=87%@3A31p[6G1pZ8H1p[DD1").
Proof.
intros mem b l. apply functional_extensionality. intro a.
unfold apply_zeros, zeros_cover, zmem. cbn [existsb fst snd].
rewrite orb_false_r. reflexivity.
Qed.
Lemma zmem_out : ltac2:(TCodec.tc2 tcn__AllocSim "Q3'VMyR0%211'<y8%511%311p051'G&TB&W0r1%22;1r3%42=1%6231&T@&T>r2%92B1%3261%5219%>271'C&T3r5r4%3421>9%31:%63G21p081pYHM1p[6N1pZ8O1p[DK1").
Proof.
intros mem b l a Hd. unfold zmem.
destruct Hd as [Hd | Hd].
- assert (E : (bv_unsigned b <=? bv_unsigned a)%Z = false) by (apply Z.leb_gt; lia).
rewrite E. reflexivity.
- assert (E : (bv_unsigned a <? bv_unsigned b + bv_unsigned l)%Z = false)
by (apply Z.ltb_ge; lia).
rewrite E, andb_false_r. reflexivity.
Qed.
Lemma rdn_zmem_out : ltac2:(TCodec.tc2 tcn__AllocSim "QK'9'Q4%211'VMyR0%211'<y8%511%311p051':&T@&T>&W0r2%22<1&TEr1%211%7241&TF+2+R0%3221%=251'Gr3%>2H1%<1>%A221r5%B2L1%E231r4%E2O1%G241%I219%<251'C%Q81Q0%Q311&T:r8&T3r7r6%3321@%6451>E%7464?F%;3921p0=1p0K1p[NQ:1pYHQA1p[6QB1pZ8QC1p[DQ?1p]>QH1").
Proof.
intros segs mem b l a n Hnw Hd. apply rdn_ext; [exact Hnw|].
intros x Hx. apply zmem_out. lia.
Qed.
Lemma rdn_zmem_in1 : ltac2:(TCodec.tc2 tcn__AllocSim "QE'9'Q4%211'VMyR0%211'<y8%511%311p051'B&T@&W0r3%22;1r1%42=1%6231&TB&T>r2%92B1%3281%5271%>271'C%K1C%F11&T:r6&T3r5r4%3321Du1%7462?1(3(7&VLz%22Q21(;%11Q3%63Q431%82B1%D3B:1p0F1pYHQ;1p[6Q<1pZ8Q=1p[DQ91p]>QB1").
Proof.
intros segs mem b l a [Hlo Hhi]. cbn [rdn]. unfold zmem.
rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
reflexivity.
Qed.
Lemma wbytes_app : forall {bs1 bs2 : list byte} m (a : word),
wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (a + nat_to_word (length bs1)) bs2.
Proof.
induction bs1 as [|b bs1 IH]; intros bs2 m a.
- cbn [app wbytes length].
replace (a + nat_to_word 0) with a; [reflexivity|].
symmetry. exact (word_add_0_r a).
- cbn [app wbytes length].
rewrite IH, word_add_nat_S. reflexivity.
Qed.
Lemma with_vmmaps_fds : ltac2:(TCodec.tc2 tcn__AllocSim "E'R:'R7'C'9'>'VMyR0%211'R5%5221%711&RG&S>r2r1%3221%511%613%@3821p[<B1p[0D1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_fs : ltac2:(TCodec.tc2 tcn__AllocSim ">'R:'R7'C&Q2&RH&S>r2r1%3221%511%613%93821p[<;1p[0=1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_halted : ltac2:(TCodec.tc2 tcn__AllocSim "B'R:'R7'C'<'VMyR0%211%411&RI&S>r2r1%3221%511%613%=3821p[<?1p[0A1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_vm : ltac2:(TCodec.tc2 tcn__AllocSim "<'R:'R7'C&RK&S>r2r1%3221%511%73914p[<91p[0;1").
Proof. reflexivity. Qed.
Lemma with_vmmaps_lazy : ltac2:(TCodec.tc2 tcn__AllocSim "D'R:'R7'C'9'>'VMyR0%211%4211%611&RJ&S>r2r1%3221%511%613%?3821p[<A1p[0C1").
Proof. reflexivity. Qed.
Lemma fd1chan_with_vmmaps : ltac2:(TCodec.tc2 tcn__AllocSim "='R:'R7&T5r1%211&S>r3r2%3221%711p061p[<:1p[0<1").
Proof. intros h m H. unfold fd1chan in *. exact H. Qed.
Lemma fd1chan_forget_vm_ranges : ltac2:(TCodec.tc2 tcn__AllocSim "C'9'>'VMyR0%211%4211%611'R7&T5r1%211&SEr3r2%3221%711p061p[<:1p\@<1").
Proof.
induction ranges as [|[a n] ranges IH]; intros m H; cbn [forget_vm_ranges].
- exact H.
- apply IH. unfold fd1chan, vm_forget_range, with_vm_backing in *.
cbn [m_fds m_fd] in *. exact H.
Qed.
Lemma adv_brk : ltac2:(TCodec.tc2 tcn__AllocSim "R8&SFy5'VMyR0%211%5241'<y8%611%311p061'9'>%1299%311'C'Q>&QB&QC(Q=r7&T8vU=%211r6(3r5%22G1(0%11I&T7%119r4r3%?8>;:75321(RLr2(;%K1N%K2Q31%311r1%51M'R6%711':%Q22Q:1%:11%=6<87641%O2?1%Q111&T9&T;(VK+:(A%33QG21%53Q51E&T<+4%22Q41&QD%12NE%<5Q9631N%QA3Q@>1p^FQC1p\<QN1p]2QI1p[DQJ1p^BR11p\8R21p\DR21").
Proof.
intros regs pc x8 mem rom r zs.
unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
cbv beta iota zeta.
cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
eff_ret eff_writes eff_zeros apply_writes].
unfold mkst, regupd.
rewrite b_npc4. reflexivity.
Qed.
Lemma in_sysno_sys_input214 : ltac2:(TCodec.tc2 tcn__AllocSim "C'9'Q4%211'Q>'VMyR0%211'C&RD&R2r3r2r1%43321%611%83913p^B:1p[J>1p]>@1").
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input214 : ltac2:(TCodec.tc2 tcn__AllocSim "F'9'Q4%211'Q>'VMyR0%211'C&R?&R2r3r2r1%43321(1%7221&Q?%1263%;3<31p^B=1p[JA1p]>C1").
Proof. reflexivity. Qed.
Lemma syscall_spec_brk : ltac2:(TCodec.tc2 tcn__AllocSim "Q7'9'Q4%211'Q>'VMyR0%211'R7'Q8'R9%211'C'J&W0r3%22:1+VF%63521&E&R3&R2r6r5r4%43321r2%732<1&SB&Q?(1%2281%4417A6%>261p0@1p\2H1p[FL1p^BN1p[JQ21p]>Q41").
Proof.
intros segs ms x8 model o Hno. unfold syscall_spec, dispatch.
rewrite in_sysno_sys_input214, Hno. reflexivity.
Qed.
Definition vm_model (h : VmMaps) : Model :=
mkModel [] h IEof [] None None None.
Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
Mmap.brk_grow_ok (vm_model h) req r.
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
Mmap.brk_r_ok (vm_model h) req r = true.
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
Mmap.brk_r_ok m req r = true.
Definition brk_model (req r : word) (m : Model) : Model :=
with_brk_next m req r.
Lemma fd1chan_brk_model : ltac2:(TCodec.tc2 tcn__AllocSim "A'VMyR0%211'R7&T5r1%211&SMr4r3r2%43321%811p071p[<;1p\<=1p\F>1").
Proof.
intros req r m H. unfold brk_model, with_brk_next. cbv zeta.
apply fd1chan_forget_vm_ranges, fd1chan_with_vmmaps, H.
Qed.
Lemma check_brk_ok_inv : ltac2:(TCodec.tc2 tcn__AllocSim "QO'VMyR0%211'R9'R7'9'R>%211'C'Q1&Or5r4r3%43321(Q0r2r1%3221%;3:51'B(RL&R=%11<(;'>y8%K11%G11%42K1%611&SDr6&S6&RK%11G%311%635>1&SC%12@3'R6%A11':%B2Q91%D11%H6F?8641%Q63Q;Q31%G1Q9%Q83Q9Q01&SO%13Q6BK&SM%13DMQ8%Q=3QAQ81%Q2241%Q3271%Q42:1p0Q61pZJQC1p[>QG1p[<QH1pZHQJ1p\FQL1").
Proof.
intros req [r ws zs us cs copyins] m m' evs H.
unfold check_brk in H.
destruct ws as [|? ?]; [|discriminate].
destruct cs as [|? ?]; [|discriminate].
destruct copyins as [|? ?]; [|discriminate].
destruct (Mmap.brk_r_ok m req r) eqn:HR; [|cbn [andb] in H; discriminate].
destruct (listNN_eqb zs (brk_zeros req r (vm_brk (m_vmmaps m)))) eqn:HZ;
[|cbn [andb] in H; discriminate].
destruct (listNN_eqb us (brk_unmaps r (vm_brk (m_vmmaps m)))) eqn:HU;
[|cbn [andb] in H; discriminate].
cbn [andb] in H.
apply listNN_eqb_eq in HZ. subst zs.
apply listNN_eqb_eq in HU. subst us.
inversion H; clear H; subst.
cbn [eff_ret]. unfold brk_resolution_ok, brk_model.
repeat split; try reflexivity. exact HR.
Qed.
Lemma check_brk_ok_intro : ltac2:(TCodec.tc2 tcn__AllocSim "Q@'VMyR0%211'R7&SOr1r3r2%43321'C'Q1&Or4(RL(;'>'9y8%B11%311%52B1%711&SD&S6&RK%11B%311%53?E1&SC%12G3'R6%A11':%B2O1%D11%F6M>8641%I3H1M(Q0&SM%13KQ1Q0'R>%K11%5231%Q23Q171p0Q41p[<Q:1p\<Q<1p\FQ=1").
Proof.
intros req r m HR. unfold brk_resolution_ok in HR.
unfold check_brk. rewrite HR.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl).
unfold brk_model. reflexivity.
Qed.
Lemma brk_ok_iff : ltac2:(TCodec.tc2 tcn__AllocSim "R?'9'Q4%211'Q>'VMyR0%211'R7'R9'R>%:11'C'J&W0r5%22:1+VF%63521&E&R3&R2r8r7r6%43321(Q6r4r3r2%44E321%;36@1'B(RL&R=%118(;'>y8%Q211%Q711%42Q21%611&SD&Q?(1%22G1&S6&RK%11Q2%311%835@1&SC%12B3'R6%C11':%D2QB1%F11%J6HA8641%Q@3QCQ11%I1QC%QB3QCQ11&SO%13QABM&SM%13DOQC%QG3QKQ71%Q4241%Q5271%Q62:1%QD2Q81p0QF1pZJQN1p[HR21pZHR21p[FR41p^BR61p[JR:1p]>R<1").
Proof.
intros segs ms x8 model eff model' evs Hno. split.
- intro H. apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
apply check_brk_complete_ok in H.
apply check_brk_ok_inv in H. exact H.
- intros (Heff & -> & Hok & ->).
apply (proj2 (syscall_spec_brk _ _ _ _ _ Hno)). apply check_brk_sound_ok.
rewrite Heff at 1. cbn [eff_ret].
apply check_brk_ok_intro. exact Hok.
Qed.
Lemma brk_ok_intro : ltac2:(TCodec.tc2 tcn__AllocSim "R2'9'Q4%211'Q>'VMyR0%211'R7'C'J&W0r3%2271+VF%63521&SO&Q?r5(1%3221r2%63:21&R3&R2r7r6%33219r4(Q6'R9(RL(;'>y8%N11%Q311%42N1%611&SD%G2>E&S6&RK%11?%311%635Q11&SC%12Q33'R6%A11':%B2Q<1%D11%F6Q9?8641&SM%13?Q;K'R>%I11%M4L531%Q43Q0O1p0Q61p0Q>1p\<QG1p[FQG1p^BQI1p[JQM1p]>QO1").
Proof.
intros segs ms x8 model r Hno Hok.
apply (brk_ok_iff segs ms x8 model _ _ _ Hno). cbn [eff_ret]. auto.
Qed.
Lemma brk_no_unmodeled : ltac2:(TCodec.tc2 tcn__AllocSim "Q0'9'Q4%211'Q>'VMyR0%211'R7'C'J&W0r2%2271+VF%63521&F&R3&R2r5r4r3%43321(Q7'R9%211%934>1%;11p0=1p[FE1p^BG1p[JK1p]>M1").
Proof.
intros segs ms x8 model Hno H.
apply (proj1 (syscall_spec_brk _ _ _ _ _ Hno)) in H.
apply (check_brk_complete_unmodeled _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in H.
unfold check_brk in H.
destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (Z_to_bv 64 0)
&& listNN_eqb []
(brk_zeros (ms_gpr ms 0) (Z_to_bv 64 0) (vm_brk (m_vmmaps model)))
&& listNN_eqb []
(brk_unmaps (Z_to_bv 64 0) (vm_brk (m_vmmaps model))));
discriminate.
Qed.
Lemma brk_receptive : ltac2:(TCodec.tc2 tcn__AllocSim "Q8'9'Q4%211'Q>'VMyR0%211'R7'C'J&W0r2%2271+VF%63521'D'R9&R3&R2r7r6r5%43321r4(Q6r1(;'R>%211%54=B41%=3871q[HH1%A2I1qZHA1%C2B1p0E1p[FM1p^BO1p[JQ31p]>Q51").
Proof.
intros segs ms x8 model Hno.
pose (r := vm_brk (m_vmmaps model)).
exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
(brk_model (ms_gpr ms 0) r model).
apply brk_ok_intro; [exact Hno|].
unfold brk_resolution_ok, Mmap.brk_r_ok, r. cbv zeta.
destruct (w_is0 (ms_gpr ms 0)
|| Z.ltb (bv_unsigned (ms_gpr ms 0))
(bv_unsigned (min_brk (m_vmmaps model)))).
- apply bv_eqb_refl.
- destruct (Z.ltb (bv_unsigned (ms_gpr ms 0))
(bv_unsigned (vm_brk (m_vmmaps model)))).
+ rewrite bv_eqb_refl, orb_true_r. reflexivity.
+ rewrite bv_eqb_refl, orb_true_r, andb_true_l.
unfold brk_grow_ok, Mmap.brk_grow_ok.
now rewrite Z.ltb_irrefl, andb_false_r.
Qed.
Lemma brk_zeros_grow : ltac2:(TCodec.tc2 tcn__AllocSim "Q9'VMyR0%211&F'Cr3&VLz%2271%53741%711&TB&W0r2%22=1%4281%42?;r4%62A1%8231'9'>%12DD%311&SDr6r5%3321:&SA&RN%11<%C2N5%311%5231%N3;71p0@1p0E1p0K1p\4Q41p\<Q51p\FQ61").
Proof.
intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
assert (E1 : w_is0 req = false)
by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
rewrite E1, E2, E3. reflexivity.
Qed.
Lemma brk_grants_grow : ltac2:(TCodec.tc2 tcn__AllocSim "Q;'VMyR0%211&F'Cr3&VLz%2271%53741%711&TB&W0r2%22=1%4281%42?;r4%62A1%8231'9'>%12DD%311&S?r6r5%3321:(7(=&VO%13N5>%34NN?1(;%11<%73=31%Q03=91p0B1p0G1p0M1p\4Q61p\<Q71p\FQ81").
Proof.
intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
assert (E1 : w_is0 req = false)
by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
rewrite E1, E2, E3. reflexivity.
Qed.
Lemma brk_zeros_query : ltac2:(TCodec.tc2 tcn__AllocSim "D'VMyR0%211'C'9'>%1244%311&SD&VLz%22:1r2r1%63321(;%11:%>3:31p\4@1p\<A1").
Proof.
intros r old. unfold brk_zeros, brk_is_grow, w_is0.
rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma brk_grants_query : ltac2:(TCodec.tc2 tcn__AllocSim "D'VMyR0%211'C'9'>%1244%311&S?&VLz%22:1r2r1%63321(;%11:%>3:31p\4@1p\<A1").
Proof.
intros r old. unfold brk_grants, brk_is_grow, w_is0.
rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma brk_zeros_keep : ltac2:(TCodec.tc2 tcn__AllocSim "A'VMyR0%211'C'9'>%1244%311&SDr2r1%33211(;%117%;3731p\4=1p\F>1").
Proof.
intros req old. unfold brk_zeros, brk_is_grow.
rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.
Lemma brk_grants_keep : ltac2:(TCodec.tc2 tcn__AllocSim "A'VMyR0%211'C'9'>%1244%311&S?r2r1%33211(;%117%;3731p\4=1p\F>1").
Proof.
intros req old. unfold brk_grants, brk_is_grow.
rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.
Lemma brk_unmaps_keep : ltac2:(TCodec.tc2 tcn__AllocSim "?'VMyR0%211'C'9'>%1244%311&SCr1%2211(;%116%:3631p\4<1").
Proof.
intros old. unfold brk_unmaps. cbv zeta.
destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.
Lemma brk_unmaps_query : ltac2:(TCodec.tc2 tcn__AllocSim "H'R:'VMyR0%211'Cr1&S6r2%211%53641'9'>%1299%311&SCr3%:11%32:1(;%117%@3731p0<1p\<C1p[0G1").
Proof. intros h r ->. apply brk_unmaps_keep. Qed.
Lemma brk_unmaps_grow : ltac2:(TCodec.tc2 tcn__AllocSim "H'VMyR0%211&T@&W0r1%2251r2%4271%6231'C'9'>%12;;%311&SCr3%221:(;%116%:3631p0<1p\4D1p\<E1").
Proof.
intros r old H. unfold brk_unmaps. cbv zeta.
destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
assert (E : (page_round_up_Z (bv_unsigned r)
<? page_round_up_Z (bv_unsigned old))%Z = false)
by (apply Z.ltb_ge, page_round_up_Z_mono, H).
unfold brk_page_range. rewrite E. reflexivity.
Qed.
Lemma brk_grow_ok_grow : forall h req r,
req <> Z_to_bv 64 0 ->
(0 < bv_unsigned (vm_brk h))%Z -> (bv_unsigned (vm_brk h) < bv_unsigned r)%Z ->
brk_grow_ok h req r
= ((if (page_round_up_Z (bv_unsigned (vm_brk h))
<? page_round_up_Z (bv_unsigned r))%Z
then (page_round_up_Z (bv_unsigned r) <=? alloc_top h)%Z
&& region_free (vm_reserved h ++ vm_maps h)
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (vm_brk h))))
(Z_to_bv 64 (page_round_up_Z (bv_unsigned r) + page_size
- page_round_up_Z (bv_unsigned (vm_brk h))))
else true)
&& (vm_backed_bytes h + bv_unsigned (r - vm_brk h) <=? vm_limit h)%Z)%bool.
Proof.
intros h req r Hreq H0 Hlt.
assert (Hmaps : m_vmmaps (vm_model h) = h) by reflexivity.
assert (Hbacked : vm_backing_used (vm_model h) = vm_backed_bytes h).
{ unfold vm_backing_used, vm_model.
cbv [mkModel m_vmmaps m_vm m_vm_lazy m_vm_materialized
vmst_lazy vmst_materialized].
change ((live_bytes (vm_backed_maps h) + 0)%Z =
live_bytes (vm_backed_maps h)).
apply Z.add_0_r. }
unfold brk_grow_ok, Mmap.brk_grow_ok, Mmap.brk_budget_ok.
rewrite Hmaps, Hbacked.
assert (E2 : (0 <? bv_unsigned (vm_brk h))%Z = true) by (apply Z.ltb_lt; lia).
assert (E3 : (bv_unsigned (vm_brk h) <? bv_unsigned r)%Z = true)
by (apply Z.ltb_lt; lia).
rewrite E2, E3. reflexivity.
Qed.
Lemma brk_grow_ok_keep : ltac2:(TCodec.tc2 tcn__AllocSim "@'R:'VMyR0%211'C'6&SLr2r1&S6%113%53431(@%93821p\F;1p[0?1").
Proof.
intros h req. unfold brk_grow_ok, Mmap.brk_grow_ok.
cbv [vm_model mkModel m_vmmaps m_vm vm_backing_used m_vm_lazy
m_vm_materialized vmst_lazy vmst_materialized].
cbn [vmst_maps vm_backed_bytes maps_subtract_all].
rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.
Lemma page_round_up_Z_aligned : ltac2:(TCodec.tc2 tcn__AllocSim "B'J&T@zr1%3221'C&TCr2&RO%3221%53:18&RNr3%211%93>12p051p0<1p^DA1").
Proof.
intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
replace (z + 4096 - 1)%Z with
(4095 + (z / 4096) * 4096)%Z by lia.
rewrite Z.div_add by lia.
rewrite Z.div_small by lia. lia.
Qed.
Lemma page_round_up_Z_bounds : ltac2:(TCodec.tc2 tcn__AllocSim "D'J&T@zr1%3221'Br2&RN%112%8231&TG&T>&RO%2271+1%5221%?281%<281p0>1p^DC1").
Proof.
intros z Hz. unfold page_round_up_Z, page_size.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
lia.
Qed.
Lemma round8_le_page_round : ltac2:(TCodec.tc2 tcn__AllocSim "C'J&T@zr1%3221&TD&T?&T>r2+7%3221+8%6221%8212&RN%117%?231p0=1p^DB1").
Proof.
intros z Hz. unfold page_round_up_Z.
pose proof (Z.div_mod (z + 7) 8 ltac:(lia)) as H8.
pose proof (Z.mod_pos_bound (z + 7) 8 ltac:(lia)) as H8mod.
pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hp.
pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hpmod.
assert (H8ceil :
(z <= ((z + 7) / 8) * 8 <= z + 7)%Z) by lia.
assert (Hpceil :
(z <= ((z + 4096 - 1) / 4096) * 4096)%Z) by lia.
set (q8 := ((z + 7) / 8)%Z) in *.
set (qp := ((z + 4096 - 1) / 4096)%Z) in *.
assert (Hq : (q8 <= 512 * qp)%Z) by lia.
change (q8 * 8 <= qp * 4096)%Z.
lia.
Qed.
Lemma round8_le_page_grant : ltac2:(TCodec.tc2 tcn__AllocSim "O'J&T@zr2%3221'C&TCr4&RO%3221%53:18&TD&T?&T>+7%2281+8%5221%7212&TG&RNr5%921?%311%5213%H271p0@1p0G1p0H1p[NM1p\4N1").
Proof.
intros old n Hold Hn Hmod.
unfold page_round_up_Z, page_size in *.
pose proof (Z.div_mod old 4096 ltac:(lia)) as Holddiv.
replace (old + n + 4096 - 1)%Z with
((n + 4096 - 1) + (old / 4096) * 4096)%Z by lia.
rewrite Z.div_add by lia.
pose proof (round8_le_page_round n Hn).
unfold page_round_up_Z in *. lia.
Qed.
Lemma region_free_prefix : ltac2:(TCodec.tc2 tcn__AllocSim "O'9'>'VMyR0%211%4211%611&T@&W0r2%2271r1%4291%6231'C'6&S0r5r4%3321:(@%73621r6%73165%:3914p041p0=1pZ:G1p]@H1pZ8I1p[@H1").
Proof.
induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree;
[reflexivity|].
cbn [region_free] in Hfree |- *.
apply andb_true_iff in Hfree as [Hhead Htail].
apply andb_true_iff. split; [|eapply IH; eassumption].
apply negb_true_iff in Hhead. apply negb_true_iff.
unfold iv_overlap in Hhead |- *.
apply andb_false_iff in Hhead. apply andb_false_iff.
destruct Hhead as [Hhead|Hhead]; [left|right];
apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.
Lemma brk_grow_ok_aligned_grow : ltac2:(TCodec.tc2 tcn__AllocSim "RA'R:'VMyR0%211&F'Cr2&VLz%2271%53741%711&TB&W0&S6r4%211%42?1%62:1r5%611%82C1r3%:2E1%<231'J&TCr6%>11%@2K1&RO%5221%K371H'6&SLr7%2319A&4&TA&RN%K2Q6E%211&R;%118%6231&S0&5'>%12Q=Q=&S<%11?&S9%11A%73531%Q81C&TG&T>%12@K%Q=2QH4%4221%QE2QJ1%@3871%I2B1&S5%11M&VO%13R0Q?<%QF2R11%<241&S8%11Q3%Q1231%Q32:1%R43Q8Q51p0Q:1p0QC1p0QJ1p0R21p\<R;1p\FR<1p[0R@1").
Proof.
intros h req r Hreq Hpos Hlt Halign.
rewrite brk_grow_ok_grow by assumption.
rewrite (page_round_up_Z_aligned (bv_unsigned (vm_brk h))) by lia.
assert (Hround : (bv_unsigned (vm_brk h)
< page_round_up_Z (bv_unsigned r))%Z).
{ pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
rewrite (proj2 (Z.ltb_lt _ _) Hround).
replace (Z_to_bv 64 (bv_unsigned (vm_brk h))) with (vm_brk h).
- reflexivity.
- symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma brk_zeros_aligned_grow : ltac2:(TCodec.tc2 tcn__AllocSim "QG'VMyR0%211&F'Cr3&VLz%2271%53741%711&TB&W0r2%22=1%4281%42?;r4%62A1%8231'J&TC&RO%2251%D341A'9'>%12II%311&SDr7r6r5%43321(7(=&TG&RN%J2Q57%211%L2Q78%5221%Q42Q91%84Q9Q9;1(;%11B%<3C31%Q;3C>1p0H1p0N1p0Q31p0Q91p\4QB1p\<QC1p\FQD1").
Proof.
intros req r old Hreq Hpos Hlt Halign.
rewrite brk_zeros_grow by assumption.
rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
unfold brk_page_range.
assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
{ pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
rewrite (proj2 (Z.ltb_lt _ _) Hround).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma brk_aligned_grant_ok : ltac2:(TCodec.tc2 tcn__AllocSim "S3'9'>'VMyR0%211%4211%611'J'C&W0&VNr5r4%33:21%52;1&T>%72=5%82>5%3221%;3<51r6%;3B1:%=2C1r3%@3A21&VL&TG&RNr7%C3J19%E2K1%411%G2M4%7221%92O1%K3OH1&TB&RO%G2J1&TF+2+R0%3221%7251&T@r9r8%Q53Q<21%Q72Q=1%F11%621Q7'6&S0r;r:%Q=3QD1:%Q?2QE1%N11%Q;21E%QB2QH5%Q2221%Q42QJ1%:3981(@%QH3=21'B%QI2QOE%QI3R0>=%QK2R11%Q:11%QM2R3A%Q=221%R03R161%M2>7%QK248%O21Q?%Q02NQ@r<%J31IH%R73L1@%L33KQ3%R93N1B%A231%B271%C291%D2<1%E2>1p0G1p0Q61p0Q>1p0QG1p0R31p0R91pZBRF1p^8RG1pZNRK1p^<RL1p\<RM1p\HRL1").
Proof.
intros res r w g top ceil Hnowrap Htop Hg Hacp Hceil Hfree.
pose proof (u64_range r). pose proof (u64_range w).
pose proof (page_round_up_Z_bounds (bv_unsigned (r + w))
(proj1 (u64_range (r + w)))).
assert (Hps : (0 < page_size)%Z) by (vm_compute; reflexivity).
assert (Hu : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
bv_unsigned (Z_to_bv 64 z) = z).
{ intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. apply Z.mod_small.
split; [exact Hlo | exact Hhi]. }
assert (HgU : bv_unsigned g
= (page_round_up_Z (bv_unsigned (r + w)) - bv_unsigned r)%Z)
by (subst g; apply Hu; lia).
repeat split; rewrite ?HgU; try lia.
- apply (region_free_prefix res r w
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
- bv_unsigned r)));
[rewrite Hu by lia; lia | exact Hfree].
- apply (region_free_prefix res r g
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (r + w)) + page_size
- bv_unsigned r)));
[rewrite HgU, Hu by lia; lia | exact Hfree].
Qed.
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
: Prop :=
r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
(t = Z_to_bv 64 0 \/
(((if (page_round_up_Z (bv_unsigned r)
<? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
<=? top)%Z
&& region_free reserved
(Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
(Z_to_bv 64 (page_round_up_Z
(bv_unsigned r + bv_unsigned t)
+ page_size - page_round_up_Z (bv_unsigned r)))
else true)
&& (bv_unsigned t <=? lim)%Z)%bool = true)).
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
(bufs : list (list byte))
(r : word) : (list (list byte) * word) -> Prop :=
fun o => (o = ([], Z_to_bv 64 4)
/\ (r = Z_to_bv 64 0
\/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
\/ t <> Z_to_bv 64 0))
\/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
: (list (list byte) * word) -> Prop :=
fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
\/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).
Lemma brk_r_ok_query_iff : ltac2:(TCodec.tc2 tcn__AllocSim "C'R:'VMyR0%211&E&SNr2&VLz%2271r1%63521'C&S6%118%33<51%<251p\<>1p[0B1").
Proof.
intros h r. unfold brk_r_ok, Mmap.brk_r_ok.
cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb].
apply bv_eqb_eq.
Qed.
Lemma reserved_top_above : ltac2:(TCodec.tc2 tcn__AllocSim "O'9'>'VMyR0%211%4211%611'J&T@&S1r2%211r1%5221'H&T>&W0&8%13>>6%32@1&?%13AA9%62C1%8241r3%A221q\6E1%=3F13p0?1p\<F1p\JH1").
Proof.
induction reserved as [|[a sz] l IH]; intros r Hr; cbn [reserved_top] in *.
- constructor.
- constructor; [cbn [fst snd]; lia | apply IH; lia].
Qed.
Lemma region_free_above_top : ltac2:(TCodec.tc2 tcn__AllocSim "J'9'>'VMyR0%211%4211%611&T@&S1r3%211&W0r2%22:1%7241'C'6&S0r4%231:7(@%63521p081p[NC1p[:D1p\JC1").
Proof.
induction reserved as [|[a sz] l IH]; intros lo n Hr;
cbn [reserved_top] in *; [reflexivity|].
cbn [region_free]. unfold iv_overlap.
assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
by (apply Z.ltb_ge; lia).
rewrite E. cbn [andb negb]. apply IH. lia.
Qed.
Lemma region_free_above : ltac2:(TCodec.tc2 tcn__AllocSim "Q4'9'>'VMyR0%211%4211%611'H&T@&T>&W0&8r1%23991%42;1&?%13<<4%72>1%9241r3%:2A1%=231q\6A1%@3B14'C'6&S0r4r2%332:1(@%73621p091p[NM1p[:N1p[6M1").
Proof.
induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
cbn [region_free]. unfold iv_overlap.
assert (E : (bv_unsigned lo <? bv_unsigned a + bv_unsigned sz)%Z = false)
by (apply Z.ltb_ge; lia).
rewrite E. cbn [andb negb]. apply IH. exact Hl.
Qed.
Lemma region_free_below : ltac2:(TCodec.tc2 tcn__AllocSim "Q2'9'>'VMyR0%211%4211%611'H&T@&T>&W0r3%2291r2%42;1%6231&8r1%23>>1%92@1%<251q\6@1%?3A1;'C'6&S0r4%231@>(@%63521p081p[NK1p[:L1p[6K1").
Proof.
induction l as [|[a sz] l IH]; intros lo n Hf; [reflexivity|].
inversion Hf as [|? ? Ha Hl]; subst. cbn [fst snd] in Ha.
cbn [region_free]. unfold iv_overlap.
assert (E : (bv_unsigned a <? bv_unsigned lo + bv_unsigned n)%Z = false)
by (apply Z.ltb_ge; lia).
rewrite E, andb_false_r. cbn [negb andb]. apply IH. exact Hl.
Qed.
Lemma growable_aligned_grow : forall reserved lim top (t r : word),
(bv_unsigned r mod page_size = 0)%Z ->
(reserved_top reserved <= bv_unsigned r)%Z ->
(0 < bv_unsigned t)%Z ->
(bv_unsigned r + bv_unsigned t + page_size - 1 <= top)%Z ->
(bv_unsigned t <= lim)%Z ->
((if (page_round_up_Z (bv_unsigned r)
<? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
<=? top)%Z
&& region_free reserved
(Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
(Z_to_bv 64 (page_round_up_Z
(bv_unsigned r + bv_unsigned t)
+ page_size - page_round_up_Z (bv_unsigned r)))
else true)
&& (bv_unsigned t <=? lim)%Z)%bool = true.
Proof.
intros reserved lim top t r Halign Htop Hpos Hceil Hlim.
pose proof (proj1 (u64_range r)) as Hr0.
rewrite (page_round_up_Z_aligned (bv_unsigned r)); [|lia|exact Halign].
assert (Hru := page_round_up_Z_bounds
(bv_unsigned r + bv_unsigned t) ltac:(lia)).
assert (Hltpage :
(bv_unsigned r < page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z)
by lia.
rewrite (proj2 (Z.ltb_lt _ _) Hltpage).
apply andb_true_iff. split; [apply andb_true_iff; split|].
- apply Z.leb_le. lia.
- rewrite Z_to_bv_bv_unsigned. apply region_free_above_top. exact Htop.
- apply Z.leb_le. exact Hlim.
Qed.
Lemma brk_aslr_max_val : ltac2:(TCodec.tc2 tcn__AllocSim "5'C'J&R<+QPPPPP0%43321").
Proof. reflexivity. Qed.
Lemma brk_model_next_query : ltac2:(TCodec.tc2 tcn__AllocSim "Q4'R:'VMyR0%211'Cr1&S6r2%211%53641&S@r3&VLz%22<1%53418(RM&S<%117&S9%119&S;%11;&S=%11=&S8%11?&S:%11A&S7%11C%?8=;97H531%L3Q0A1p0H1p\<O1p[0Q31").
Proof.
intros h r ->. unfold brk_model_next, brk_maps_next.
rewrite Z.ltb_irrefl, andb_false_r.
rewrite brk_grants_query, brk_unmaps_keep. reflexivity.
Qed.
Lemma brk_model_query : ltac2:(TCodec.tc2 tcn__AllocSim "Q9'VMyR0%211'R7'Cr2&S6&RKr1%211%411%73961&SM&VLz%22>1r3%5321<&S>(RM&S<%>1@%211&S9%113&S;%115&S=%117&S8%119&S:%11;&S7%11=%@8=;97C531%B21O%Q13Q2D1p0K1p[<Q41p\<Q61").
Proof.
intros r m ->. unfold brk_model, with_brk_next. cbv zeta.
rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
rewrite brk_model_next_query by reflexivity. reflexivity.
Qed.
Lemma brk_r_ok_grow_iff : ltac2:(TCodec.tc2 tcn__AllocSim "QN'9'>'VMyR0%211%4211%611'J&TBz&W0r2%2291%5241&T@r9%62=1r3%82?1%5231r4%;2B1%8261&E&SN(RMr=r8r;r:r<r7r6%887B654321r5%;321?'B'G'C%13Q3C5%23Q4D;%4221'6&SL%13;:H(@%83421%;261%I2=1p0K1p0O1p0Q61p\>Q@1p\FQA1p]DQB1p[BQC1p\0QB1p[@QC1p\<QF1p]<QG1p[8QE1p\JQG1").
Proof.
intros reserved lim s r maps noaccess mb sp req r2 Hpos Hs Hreq.
unfold brk_r_ok, Mmap.brk_r_ok.
cbv [vm_model mkModel m_vmmaps m_vm]. cbv zeta.
assert (E0 : w_is0 req = false).
{ unfold w_is0, bv_eqb.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
apply Z.eqb_neq. lia. }
rewrite E0.
assert (Hmin : (bv_unsigned req <?
bv_unsigned (min_brk (mkVmMapsFull reserved maps noaccess s r lim mb sp)))%Z
= false).
{ apply Z.ltb_ge. unfold min_brk. cbn [vm_start_brk]. lia. }
cbn [vmst_maps]. rewrite Hmin. cbn [orb vm_brk].
rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned r)) ltac:(lia)).
rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. tauto.
Qed.
Lemma T1_iff_T2 : ltac2:(TCodec.tc2 tcn__AllocSim "RB'9'>'VMyR0%211%4211%611'Jy8%711%:11%;11&F'Cr1&VLz%22>1%53>41%711&T@&W0r7%22D1r2%42F1%6231&TB&T>r3%92K1r5%;2M1%5231&TF+2+R0%3221%;251%Q62LQ3&E&SGr<r;&TGr8%I2Q;1&S3%4221r6%97872L1CQ4'D'B&SN(RMr=(;%11QDr:r9%68533A;B21&VN%13QK=A%:331QA&SH%143Q;QCQ9%>231q\>QO1%A2R01%M2C1p\2O1p0Q11p0Q>1p0QF1p\<R61pZ>R01p^4R81p]DR91p[BR:1p]<R;1p[8R91p\JR;1").
Proof.
intros reserved lim s mb sp t bufs r Hr0 Hs Hnw o.
pose proof (u64_range r) as Hur. pose proof (u64_range t) as Hut.
pose proof (word_neq0_unsigned r Hr0) as Hur0.
assert (Huadd : bv_unsigned (r + t) = (bv_unsigned r + bv_unsigned t)%Z)
by (apply u_add_small; exact Hnw).
assert (Hwant0 : r + t <> Z_to_bv 64 0).
{ intro He. apply (f_equal bv_unsigned) in He.
rewrite Huadd in He.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in He. lia. }
assert (Bridge : forall r2,
brk_r_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2 <->
(r2 = r + t \/ r2 = r)
/\ brk_grow_ok (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t) r2
= true)
by (intro r2; apply brk_r_ok_grow_iff with (maps := []) (noaccess := []); lia).
split.
- intros [[-> Hcase] | [Hg ->]].
+
assert (Ht0 : t <> Z_to_bv 64 0)
by (destruct Hcase as [Hc | [Hc | Hc]]; [congruence | lia | exact Hc]).
pose proof (word_neq0_unsigned t Ht0) as Hut0.
exists r. split.
* apply Bridge. split; [right; reflexivity|].
exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) (r + t)).
* right. split; [| reflexivity].
intro He. apply (f_equal bv_unsigned) in He.
rewrite Huadd in He. lia.
+
destruct Hg as (_ & _ & Hb).
exists (r + t). split.
* apply Bridge. split; [left; reflexivity|].
destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz].
{ assert (Ht0 : t = Z_to_bv 64 0)
by (apply bv_eq; rewrite Hz; reflexivity).
rewrite Ht0, word_add_0_r.
exact (brk_grow_ok_keep (mkVmMapsFull reserved [] [] s r lim mb sp) r). }
destruct Hb as [Hb | Hb];
[exfalso; apply Hz; rewrite Hb; reflexivity |].
rewrite brk_grow_ok_grow;
cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes];
[| exact Hwant0 | lia | lia].
rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l.
exact Hb.
* left. split; reflexivity.
- intros (r2 & Hrok & Hb).
apply Bridge in Hrok. destruct Hrok as (Hcase & Hgrow).
destruct Hb as [[-> ->] | [Hne ->]].
+
right. split; [| reflexivity].
split; [exact Hr0 | split; [exact Hnw |]].
destruct (Z.eq_dec (bv_unsigned t) 0) as [Hz | Hz];
[left; apply bv_eq; rewrite Hz; reflexivity | right].
rewrite brk_grow_ok_grow in Hgrow;
cbn [vm_brk vm_reserved vm_maps vm_limit vm_live_bytes live_bytes] in *;
[| exact Hwant0 | lia | lia].
rewrite app_nil_r, word_add_sub_cancel, Huadd, Z.add_0_l in Hgrow.
exact Hgrow.
+
left. split; [reflexivity |].
right. right.
intro Ht0. subst t.
rewrite word_add_0_r in Hne, Hcase.
destruct Hcase as [Hc | Hc]; exact (Hne Hc).
Qed.
Lemma T2_fail_iff : ltac2:(TCodec.tc2 tcn__AllocSim "Q3'VMyR0%211'9y8%511%311%411&F'Cr1r3%33:21%511'>%128=&E&SHr5r4%34219:(=(;%11A&VL+4%22I1%64DI41%C3=B1%=291p\2?1p0B1p\>N1pZ>J1p^>Q01").
Proof.
intros want bufs r2 Hne o. unfold T2. tauto.
Qed.
Lemma T2_succ_iff : ltac2:(TCodec.tc2 tcn__AllocSim "K'VMyR0%211'9y8%511%311%411'>%1227&E&SHr3r2r1%443231'C(=&VLz%22C1%44>C81%63=81%=281p\2?1pZ>B1p^>H1").
Proof.
intros want bufs o. unfold T2. tauto.
Qed.
Section WithSegs.
Variable segs : list Segment.
Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
fd1chan model ->
to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
bufs_modeled bufs ->
(forall o, U o <-> o = (bufs, code)) ->
to_outcomes ms model U
| tou_step : forall ms ms' model U,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_outcomes ms' model U ->
to_outcomes ms model U
| tou_brk : forall ms model x8
(T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
(U : (list (list byte) * word) -> Prop),
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 214%Z ->
(forall eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
(forall o, U o <->
(exists eff model' evs,
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
/\ T eff model' o)) ->
to_outcomes ms model U.
Lemma tou_msteps : ltac2:(TCodec.tc2 tcn__AllocSim "N'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'T6vVFr4r3%43321'SKr2%23541r6%43176p031p071pYD=1p[FJ1p[LL1p[JM1").
Proof.
intros ms ms' model U H; induction H; [auto|].
intro Ht. eapply tou_step; eauto.
Qed.
Lemma forget_vm_ranges_frame : ltac2:(TCodec.tc2 tcn__AllocSim "Q?'9'>'VMyR0%211%4211%611'R7'B'C'<%117&RI&SEr2r1%3221%511%613%:3821&Q2&RH%116%218%?3421'R5%I2F1%K11&RG%11=%21?%F3421&RJ%11B(;%11N%K3N31r3%I21H%711%O3Q215p051%Q22;1%Q32C1%Q42I1p[FQ61p\@Q81").
Proof.
induction ranges as [|[a n] ranges IH]; intros model; cbn [forget_vm_ranges].
- auto.
- specialize (IH (vm_forget_range (bv_unsigned a)
(bv_unsigned a + bv_unsigned n) model)).
destruct IH as (Hhalt & Hfs & Hfds & Hlazy).
unfold vm_forget_range, with_vm_backing in Hhalt, Hfs, Hfds, Hlazy.
cbn [m_halted m_fs m_fds m_vm_lazy] in Hhalt, Hfs, Hfds, Hlazy.
repeat split; try assumption.
intro Hempty. apply Hlazy. rewrite Hempty. reflexivity.
Qed.
Lemma brk_step_shape : ltac2:(TCodec.tc2 tcn__AllocSim "R='Q>'VMyR0%211'R7'R9'9'R>%211'C'<%118&RIr4%211(0%11=%83631'>%12@@%>11&RJr5%211(;%116%A3631'J&W0r7%22L1+VF%G3521&R3&R2vVFr9r8%43321(Q6r6%24Q41CL%934=1'B%D1Q5%Q43Q5G1%Q216%Q63Q41O&Q2&RH%11:%21>%Q;3421'R5%Q42QC1%QA11&RG%11A%21E%QB3421%Q71D%Q81H%QE3Q:21%D241%E2<1%F2B1%G2E1p0I1p0Q41p0Q;1p0QE1pZJQO1p[HR41pZHR41p[FR61p^BR81p[JR<1").
Proof.
intros ms x8 model eff model' evs Hh Hlazy Hno Hs.
apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hs.
destruct Hs as (_ & -> & _ & ->).
unfold brk_model, with_brk_next. cbv zeta.
destruct (forget_vm_ranges_frame
(brk_unmaps (eff_ret eff) (vm_brk (m_vmmaps model)))
(with_vmmaps
(brk_model_next (m_vmmaps model) (ms_gpr ms 0) (eff_ret eff)) model))
as (Hhalt & Hfs & Hfds & Hlazy').
repeat split.
- rewrite Hhalt. unfold with_vmmaps. cbn [m_halted]. exact Hh.
- rewrite Hfs. unfold with_vmmaps. reflexivity.
- rewrite Hfds. unfold with_vmmaps. reflexivity.
- rewrite Hlazy. apply Hlazy'.
unfold with_vmmaps. cbn [m_vm_lazy]. exact Hlazy.
Qed.
Lemma sstep_brk_inv : ltac2:(TCodec.tc2 tcn__AllocSim "RF'Q>'R7'VMyR0%211'9'R>%211'R1'C'<%117&RIr4%211(0%11<%83631'>%12??%?11&RJr5%211(;%116%A3631&Q@r7%211(3%12K9%G3E31'J&W0r6%22Q11+VF%M3521'QOvVF(QIr9r8%3221%6451:G'D'R9'B&R3&R2r<r:%33=21r;(Q6r2r1%Q21QD%44<321%;3761%QD3QFC3(QA&QB&QC%12>9%311%J21:%611%QL3QMJ1%F291%G2;1q[HR71%K2R81qZHK1%M2L1p0O1p0Q71p0Q>1p0QE1p0QO1p]FR91pZJR;1p^BR?1p[FRC1p[JRE1").
Proof.
intros ms model x8 evs st Hh Hlazy Hsvc Hno Hss.
inversion Hss; subst; try congruence.
-
assert (Hx : x0 = x8) by congruence; subst x0.
destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno H3)
as (He & _ & _ & _ & Hlazy').
subst evs.
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans Hlazy' Hlazy)) in H7.
inversion H7; subst model''.
exists eff, model'; auto.
-
exfalso.
match goal with
| Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec)
as (He & _ & _ & _ & Hlazy'); subst evs0;
rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)) in Hmat;
discriminate
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hhalt : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
congruence
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hkill : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (brk_step_shape ms x8 model eff model' evs0 Hh Hlazy Hno Hspec) as (_ & Hm & _ & _);
assert (Hhn : m_halted model' = None) by congruence;
rewrite (m_killed_of_m_halted_none _ Hhn) in Hkill; discriminate
end.
-
exfalso.
match goal with
| Hsvc' : ms_svc_pending ms = Some ?x,
Hspec : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (brk_no_unmodeled segs ms x8 model Hno Hspec)
end.
Qed.
Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
wevents (fst o) ++ [ExitEv (snd o) fs].
Definition outcomes_post (fs : Fs.Fs) (U : (list (list byte) * word) -> Prop) : post :=
fun tr o => exists out, U out /\ tr = outcome_trace fs out /\ exits_with (snd out) tr o.
Lemma to_outcomes_exec : ltac2:(TCodec.tc2 tcn__AllocSim "QD'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631'Q:vVF(QIr6r5%3221&SJ&RH%114%321>%:3951p0<1p0E1p0N1pYDQ41p[FQA1p[JQC1").
Proof.
intros ms model U Hto.
induction Hto as
[ ms model bufs code U Hfd Hte Hbm HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hno Hcont IH HU ];
intros Hh Hlazy.
-
eapply exec_conseq;
[exact (to_wallexit_exec segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 bufs code ms model
Hh Hlazy (fd1chan_fdchan model Hfd) Hbm Hte) |].
intros tr o (Heq & Hx). exists (bufs, code).
split; [apply HU; reflexivity |].
split; [unfold outcome_trace; cbn [fst snd]; rewrite <- wevents_ch_fd1; exact Heq |].
cbn [snd]. exact Hx.
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hh Hlazy) |]. intros tr o H. cbn [app]. exact H.
-
apply exec_step; [exact Hh | | |].
+ destruct (brk_receptive segs ms x8 model Hno) as (eff & model' & Hspec).
destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
as (_ & Hh' & _ & _ & Hlazy').
eexists; eexists.
apply (sstep_syscall segs ms model x8 eff model' model' []); try assumption.
rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans Hlazy' Hlazy)). reflexivity.
+ intros evs Hss.
destruct (sstep_brk_inv ms model x8 evs SError Hh Hlazy Hsvc Hno Hss)
as (eff & model' & _ & _ & Habs). discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_brk_inv ms model x8 evs (SNext c') Hh Hlazy Hsvc Hno Hss)
as (eff & model' & Hspec & -> & Hc'). injection Hc' as ->.
destruct (brk_step_shape ms x8 model eff model' [] Hh Hlazy Hno Hspec)
as (_ & Hh' & Hfs & _ & Hlazy').
eapply exec_conseq; [exact (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy)) |].
intros tr o (out & Hout & Heq & Hx). exists out.
split; [apply HU; exists eff, model', []; split; [exact Hspec | exact Hout] |].
split; [| exact Hx].
cbn [app]. unfold outcome_trace in Heq |- *. rewrite Hfs in Heq. exact Heq.
Qed.
Lemma to_outcomes_no_other_exit : ltac2:(TCodec.tc2 tcn__AllocSim "QN'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631r6%11C&F&?%13OMG%E3N1I%411p061p\2Q01'Q:vVF(QIr8r7%3221&Q;%11Q3%83731%@11p0;1pZFQ=1p0F1p0O1p0Q81pYDQ>1p[FQK1p[JQM1").
Proof.
intros ms model U Hto Hh Hlazy code' Hne Hex.
destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
as (tr & [c' | c'] & Hm & (out & Hout & _ & Hx)); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'.
exact (Hne out Hout Hx').
Qed.
Lemma to_outcomes_not_silent : ltac2:(TCodec.tc2 tcn__AllocSim "QG'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631&F'Q9vVF(QIr6r5%3221'R>%Q811%<12%J32L1q^:31%;3:61%=11p0?1p0H1p0Q11pYDQ71p[FQD1p[JQF1").
Proof.
intros ms model U Hto Hh Hlazy Hc.
destruct (exec_realizes _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy))
as (tr & [c' | c'] & Hm & (out & _ & Heq & Hx)); [| destruct Hx].
destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
subst tr. unfold outcome_trace in Hnil.
destruct (wevents (fst out)); discriminate Hnil.
Qed.
Lemma to_outcomes_star_only : ltac2:(TCodec.tc2 tcn__AllocSim "R3'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631'R>%Q111'QE'R0vVF(QIr8r7%3221%6451LK'D'B%61N&QH&SI&RHr9%211%421Q4%63CH1%9281q\2Q=1%<2Q>1p0>1pZ@F1p^:H1p0K1p0Q41p0Q=1pYDQC1p[FR01p[JR21").
Proof.
intros ms model U Hto Hh Hlazy tr c Hstar.
destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_outcomes_exec ms model U Hto Hh Hlazy) Hstar))
as (tr' & o & _ & (out & Hout & Heq & _)).
exists out. split; [exact Hout |]. rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_outcomes_star_admits : ltac2:(TCodec.tc2 tcn__AllocSim "QL'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631r5%11C'D'QE'R0vVF(QIr9r8%3221&SI&RH%114%321Q1%:4951Q0qZ@<1%>2=1p0@1p\2Q:1p0D1p0M1p0Q61pYDQ<1p[FQI1p[JQK1").
Proof.
intros ms model U Hto.
induction Hto as
[ ms model bufs code U Hfd Hte Hbm HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hno Hcont IH HU ];
intros Hh Hlazy o Ho.
-
apply HU in Ho. subst o.
unfold outcome_trace; cbn [fst snd].
rewrite <- wevents_ch_fd1.
eapply (to_wallexit_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1);
[exact Hh | exact Hlazy | exact (fd1chan_fdchan model Hfd)
| exact Hbm | exact Hte].
-
destruct (IH Hh Hlazy o Ho) as [c Hstar].
exists c.
replace (outcome_trace (m_fs model) o)
with ([] ++ outcome_trace (m_fs model) o) by reflexivity.
eapply star_step; [|exact Hstar].
apply (sstep_instr segs ms model ms' model); [assumption | assumption |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
-
apply HU in Ho.
destruct Ho as (eff & model' & evs & Hspec & Ht).
destruct (brk_step_shape ms x8 model eff model' evs Hh Hlazy Hno Hspec)
as (Hevs & Hh' & Hfs & _ & Hlazy'). subst evs.
destruct (IH eff model' [] Hspec Hh' (eq_trans Hlazy' Hlazy) o Ht)
as [c Hstar].
exists c.
replace (outcome_trace (m_fs model) o)
with ([] ++ outcome_trace (m_fs model') o)
by (unfold outcome_trace; rewrite Hfs; reflexivity).
eapply star_step; [|exact Hstar].
apply (sstep_syscall segs ms model x8 eff model' model' []);
try assumption.
rewrite (materialize_model_accesses_no_lazy _ _
(eq_trans Hlazy' Hlazy)).
reflexivity.
Qed.
Lemma to_outcomes_no_error : ltac2:(TCodec.tc2 tcn__AllocSim "QB'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021'SKr3r2r1%43321'C'<%11;&RI%118(0%11?%73531%I2AA%I11&RJr4%211(;%116%?3631&F&QLvVF(QIr6r5%3221%6251%811p0:1p0C1p0L1pYDQ21p[FQ?1p[JQA1").
Proof.
intros ms model U Hto Hh Hlazy. apply exec_no_error.
eapply exec_conseq; [exact (to_outcomes_exec ms model U Hto Hh Hlazy) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma tou_brk_r : ltac2:(TCodec.tc2 tcn__AllocSim "S0'Q>'R7'VMyR0%211'>'9y8%611%311%411%6217!p021p0:1p^@43'C'<%11>&Q@r5%211(3r3%22D1%93741'J&W0r4%22J1+VF%?3521&SOr7&Q?r8(1%3221r1%73621'SK&QB&QCr9(RLr2(;%Q:2Q;Q6%211&SD%@27>&S6&RK%11B%311%635:1&SC%12<3'R6%=11':%QH2QI1%@11%C6B?8641%F2E1%H11&SM%13AFQ0r6%11H%N3531p0Q01p\<R41&E%QF1Q4'D'Br:%Q<21Q:%Q?3Q41Q9%Q?2Q:Q3%5221q\<R>1%82R?1%;2:1p\2R:1%Q>3Q;QCR2p021p0@1p0QJ1p0R11pYDR<1pYBR>1p^BRI1p[FRM1p[JRO1").
Proof.
intros ms model x8 T' U Hsvc Hno Hcont HU.
apply (tou_brk ms model x8 (fun eff _ => T' (eff_ret eff)) U);
[exact Hsvc | exact Hno | |].
- intros eff model' evs Hspec.
apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
destruct Hspec as (Heff & _ & Hok & ->).
pose proof (Hcont (eff_ret eff) Hok) as H.
rewrite <- Heff in H. exact H.
- intro o. rewrite HU. split.
+ intros (r & Hok & Ht).
exists (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] []),
(brk_model (ms_gpr ms 0) r model), [].
split; [apply brk_ok_intro; [exact Hno | exact Hok] | exact Ht].
+ intros (eff & model' & evs & Hspec & Ht).
apply (brk_ok_iff segs ms x8 model eff model' evs Hno) in Hspec.
destruct Hspec as (_ & _ & Hok & _).
exists (eff_ret eff). auto.
Qed.
Lemma tou_wexit_eq : ltac2:(TCodec.tc2 tcn__AllocSim "Q;'Q>'R7'9'VMy8%211%411%511yR0%611&T5r3%211&T=vVF&VL+1%2291r2r5%7563921&T4r4%211'SKr7r6'>%12EC'Cr1(=%14IG6=%43531q\261%;3:91p0=1p0A1p0J1pZDN1pZ>Q11p[FQ81p[JQ:1").
Proof.
intros ms model bufs code Hfd Hte Hbm.
apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm | tauto].
Qed.
Lemma tou_equiv : ltac2:(TCodec.tc2 tcn__AllocSim "Q3'Q>'R7'>'9'VMy8%211%411%511yR0%611%9231!p021p^@32'SKr4r3r2%43321&Er1%511%712%4221p\2>1r6r5%=321;p041p0;1pYFA1pYDC1p[FQ01p[JQ21").
Proof.
intros ms model U V Hto; revert V.
induction Hto as
[ ms model bufs code U Hfd Hte Hbm HU
| ms ms' model U Hsvc Hstep Hto IH
| ms model x8 T U Hsvc Hno Hcont IH HU ];
intros V HV.
- apply (tou_wexit ms model bufs code); [exact Hfd | exact Hte | exact Hbm |].
intro o. rewrite (HV o). apply HU.
- eapply tou_step; [exact Hsvc | exact Hstep | apply IH; exact HV].
- apply (tou_brk ms model x8 T V); [exact Hsvc | exact Hno | |].
+ intros eff model' evs Hspec. exact (Hcont eff model' evs Hspec).
+ intro o. rewrite (HV o). apply HU.
Qed.
End WithSegs.
Lemma alloc_omni_run : ltac2:(TCodec.tc2 tcn__AllocSim "R3'9'Q4%211'I'Q3'VMyR0%211'R4'J'R8'>y8%811%>11%?11%5219!p021'T2r:&QGr9r8r7r4&R@r2%211&RA%113&RE%115&RC%117%>9?=<;:7531&RF&QN%11Br6r5r3%66432B1?r1%I4H921&Q<(Q5r;%231LJ(QJ%14KJ;:&T1&RB%11<%321K%:57N5>1p0<1pYDQ71p[2Q@1p[8QB1p]0QD1p[BQF1pZ<QG1p]DQH1p\:QL1p\8QN1p]>R01").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto.
cbn [omni_run]. unfold init_config.
exact (to_outcomes_exec segs _ _ U Hto eq_refl eq_refl).
Qed.
Lemma alloc_obs_iff : ltac2:(TCodec.tc2 tcn__AllocSim "R?'9'Q4%211'I'Q3'VMyR0%211'R4'J'R8'>y8%811%>11%?11%5219!p021'T2r:&QGr9r8r7r4&R@r2%211&RA%113&RE%115&RC%117%>9?=<;:7531&RF&QN%11Br6r5r3%66432B1?r1%I4H921'R>%Q>11&E&QKr<&QFr;%2931Q0NML=<K%5341:'D'B%O1=&QH&T0&RB%11D%321B%53AQ31%8271q\2Q@1%;2QA1%C2=1p^:E1p0H1pYDQC1p[2QL1p[8QN1p]0R01p[BR21pZ<R31p]DR41p\:R81p\8R:1p]>R<1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto tr.
unfold init_config.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None)
by reflexivity.
assert (Hlazy : m_vm_lazy
(init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = in_fs inp)
by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_outcomes_star_only segs ms _ U Hto Hh Hlazy tr' c Hstar)
as (o & Ho & Hp').
exists o. split; [exact Ho|].
rewrite Hfs in Hp'. eapply is_prefix_trans; eauto.
- intros (o & Ho & Hp).
destruct (to_outcomes_star_admits segs ms _ U Hto Hh Hlazy o Ho) as [c Hstar].
rewrite Hfs in Hstar.
exists (outcome_trace (in_fs inp) o), c. split; assumption.
Qed.
Lemma alloc_no_error_run : ltac2:(TCodec.tc2 tcn__AllocSim "QO'9'Q4%211'I'Q3'VMyR0%211'R4'J'R8'>y8%811%>11%?11%5219!p021'T2r:&QGr9r8r7r4&R@r2%211&RA%113&RE%115&RC%117%>9?=<;:7531&RF&QN%11Br6r5r3%66432B1?r1%I4H921&F&QLr;&QF%192MKJI:9H8%4231%611p081pYDQ31p[2Q<1p[8Q>1p]0Q@1p[BQB1pZ<QC1p]DQD1p\:QH1p\8QJ1p]>QL1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp U Hto. apply exec_no_error.
eapply exec_conseq; [exact (alloc_omni_run segs pc ph sp brk0 mb rnd lim inp U Hto) |].
intros tr o (out & _ & _ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma alloc_omni_strong_equiv : ltac2:(TCodec.tc2 tcn__AllocSim "RH'9'Q4%211'I'Q3'VMyR0%211'R4'>y8%611%<11%=11%5217!p021'R8'T2r@&QGr?r>r=r:&R@r1%211&RA%113&RE%115&RC%117%>9?=<;:7531&RF&QN%11Br<r;&S2%66432B1?r2%I4H921r9r8r7r4%G16%E17%D18%C19%Q09L87654321%A1Mr6r5&S4%F6432;1?r3%Q94Q3721&M(Q5rBrA%3321Q=%43JQ9E(QJ%14Q>Q=Q<M%24GF>=%955421;p0;1p0L1p[2QG1pYDQI1pZ4R21pYNR41pYJR51pZ6R61pZ2R:1pZ0R<1p^6R>1p]8R91p\NR;1p\BR<1p]:R=1p]6RA1p]4RC1p]BRE1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd U inp
Hsource Htarget.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (alloc_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource) |].
intros tr o (out & _ & _ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp U Hsource tr).
rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit inp U Htarget).
Qed.
Lemma alloc_strong_equiv : ltac2:(TCodec.tc2 tcn__AllocSim "S2'9'Q4%211'I'Q3'VMyR0%211'R4'J'>y8%711%=11%>11%5218!p021'R8'T2rB&QGrAr@r?r<&R@r1%211&RA%113&RE%115&RC%117%>9?=<;:7531&RF&QN%11Br>r=r;%66432B1?r2%I4H921r:r9r8r5%G16%E17%D18%C19%Q09<87654321%A1=r7r6r4%F6432;1?r3%Q94C721'B&L&QM(Q5rDrC%3321Q?(QJ%14Q?Q>Q=N%743N1;%911&K%93Q@Q0L%64LKCB%<42K1@%4261%@261p0B1p0Q31p[2QN1pYDR01pYLR91pZ4R;1pYNR=1pYJR>1pZ6R?1pZ2RC1pZ0RE1p^6RG1p\LRA1p]8RC1p\NRE1p\BRF1p]:RG1p]6RK1p]4RM1p]BRO1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
U inp Hsource Htarget.
split.
{ apply no_error_run_modeled.
apply (alloc_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource). }
right. split.
- intro tr. cbn.
rewrite (alloc_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim inp U Hsource tr).
rewrite (alloc_obs_iff target_segs apc aph asp abrk amb arnd alim inp U Htarget tr).
reflexivity.
- cbn. apply (alloc_no_error_run target_segs apc aph asp abrk amb arnd alim inp U Htarget).
Qed.
End WithFP1.
