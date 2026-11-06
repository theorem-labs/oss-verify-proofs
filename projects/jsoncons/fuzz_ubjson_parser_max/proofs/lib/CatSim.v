(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CatSim () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.MustExit."; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.OmniRun."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim.WithSegsCh."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1cons"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2iff"]; ["2not"; "3le"; "4Forall"; "4firstn"; "4map"; "4skipn"; "5N"; "5Z"; "6equiv"; "6modeled"; "7must_exit_with"; "8omni_strong_equiv"; "9len_word"; ":check_write"; ";CheckOk"; ";check_result"]; ["<PhdrInfo"; "<Segment"; "<mkImage"; "=Ok"; "=Unmodeled"; "=outcome"; ">exec"; ">exits_with"; ">omni_run"; "?MachineOk"; "?machine_result"; "?machine_state"; "?ms_gpr"; "?ms_read_byte"; "?ms_read_bytes"; "?ms_read_bytes_aux"]; ["?ms_svc_pending"; "?set_gpr0"; "?step"; "@SNext"; "@advance_past_svc"; "@apply_effect"; "@config"; "@init_config"; "@init_machine_state"; "@is_prefix"; "@mkCfg"; "@mkEntry"; "@obs_trace"; "@reaches_error"; "@run"; "@sstep"]; ["@star"; "@step_to"; "@sys_input"; "Asyscall_spec"; "BEntryDraw"; "CExitEv"; "CMemCopy"; "CModel"; "CProcInput"; "CSyscallEffect"; "CWriteEv"; "Cevent"; "Cin_arg"; "Cin_argv"; "Cin_envp"; "Cin_fs"]; ["Cin_hwcap"; "Cin_mem"; "Cin_sysno"; "Cin_uid"; "Cinit_model"; "Cm_fs"; "Cm_halted"; "Cm_vm_lazy"; "CmkEffectU"; "Cread_bytes_aux"; "Cread_bytes_map"; "Cwith_copyins"; "Dwrite_spec"; "Efd32"; "Gmsteps"; "Gto_wexit"]; ["Gwexit_post"; "Hto_wexit_ch"; "Fbuf_modeled"; "Fbufs_modeled"; "Ffd1chan"; "Ffdchan"; "Fmsteps"; "Fto_wexit"; "Fto_wexit_ch"; "Fwevents"; "Fwevents_ch"; "Fwexit_post"; "Fwpick"; "0a"; "0abrk"; "0alim"]; ["0amb"; "0apc"; "0aph"; "0arnd"; "0asp"; "0b"; "0brk0"; "0buf"; "0bufs"; "0c"; "0c'"; "0ch"; "0code"; "0code'"; "0copyins"; "0eff"]; ["0evs"; "0fd"; "0full"; "0inp"; "0k"; "0len"; "0lim"; "0mb"; "0model"; "0model'"; "0ms"; "0ms'"; "0ms''"; "0n"; "0o"; "0pc"]; ["0ph"; "0r"; "0rbrk"; "0reserved"; "0rlim"; "0rmb"; "0rnd"; "0rpc"; "0rph"; "0rrnd"; "0rsp"; "0segs"; "0source_segs"; "0sp"; "0st"; "IZ_to_bv"]; ["Ibv"; "Ibv_unsigned"; "0target_segs"; "0tr"; "0x8"]]).
Lemma read_aux_read_byte : ltac2:(TCodec.tc2 tcn__CatSim "I'Q;'7'U0yR0%211'='9'6y8%711%311%511&RI&Q=r3%211r1r2%63321&Q?%13643%@3:31pVLB1pX:F1pXFH1").
Proof.
intros ms. induction k as [|k IH]; intro a; [reflexivity|].
cbn [read_bytes_aux ms_read_bytes_aux].
destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.
Lemma read_bytes_map_read_byte : ltac2:(TCodec.tc2 tcn__CatSim "H'Q;'U0yR0%211'='9'6y8%711%311%511&RJ&Q=r3%211r2r1%63321&Q>%13643%@3:31pX<B1pVLC1pXFG1").
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
apply read_aux_read_byte. Qed.
Lemma apply_effect_no_write : ltac2:(TCodec.tc2 tcn__CatSim "O'Q;'U0yR0%211'=&QEr2(RHr1(8';'6y8%<11%311%52<1%711%72>>%911'R6%;11'7%<2C1%>11%A6@86641%D2C1&QA%12EC%H3L31pY4J1pXFN1").
Proof.
intros ms r. unfold apply_effect, set_gpr0.
cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
reflexivity.
Qed.
Lemma apply_effect_copyins_no_write : ltac2:(TCodec.tc2 tcn__CatSim "Q4'Q;'U0yR0%211'6';'7%2241%411'=&QEr3&RKr1(RHr2(8y8%A11%?11%?2A1%511%A2CC%711'R6%911%:1C%=6<64421%@2?1%C2B1&QA%12D@%G3Q031pWNI1pY4O1pXFQ31").
Proof.
intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
apply_unmaps apply_zeros apply_copies apply_writes].
reflexivity.
Qed.
Lemma in_sysno_sys_input64 : ltac2:(TCodec.tc2 tcn__CatSim "C'6'Q1%211'Q;'U0yR0%211'=&RB&R2r3r2r1%43321%611%83913pZ::1pXF>1pYH@1").
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input64 : ltac2:(TCodec.tc2 tcn__CatSim "F'6'Q1%211'Q;'U0yR0%211'=&R<&R2r3r2r1%43321(1%7221&Q<%1263%;3<31pZ:=1pXFA1pYHC1").
Proof. reflexivity. Qed.
Lemma in_arg1_sys_input64 : ltac2:(TCodec.tc2 tcn__CatSim "F'6'Q1%211'Q;'U0yR0%211'=&R<&R2r3r2r1%43321u1%7221&Q<%1263%;3<31pZ:=1pXFA1pYHC1").
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input64 : ltac2:(TCodec.tc2 tcn__CatSim "F'6'Q1%211'Q;'U0yR0%211'=&R<&R2r3r2r1%43321u2%7221&Q<%1263%;3<31pZ:=1pXFA1pYHC1").
Proof. reflexivity. Qed.
Lemma in_mem_sys_input : ltac2:(TCodec.tc2 tcn__CatSim "J'6'Q1%211'Q;'U0yR0%211'='9y8%611%311p061&RA&R2r3r2r1%43321%611&Q=%115%?3:31pZ:A1pXFE1pYHG1").
Proof. reflexivity. Qed.
Lemma syscall_spec_write : ltac2:(TCodec.tc2 tcn__CatSim "Q='6'Q1%211'Q;'U0yR0%211'R7'Q5'R9%211'='G&U1r3%22:1+R0%63521&?&R3&R2r6r5r4%43321r2%732<1&RL&RM&Q<(1%2291%411u1%52<1u2%72>1%:6531=G<%D2<1p0F1pXNN1pXBQ21pZ:Q41pXFQ81pYHQ:1").
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Hno. reflexivity.
Qed.
Definition fd1chan (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Definition buf_modeled (b : list byte) : Prop :=
(Z.of_nat (length b) <= rw_bytes_max)%Z.
Definition bufs_modeled (bufs : list (list byte)) : Prop :=
Forall buf_modeled bufs.
Lemma bufs_modeled_single : ltac2:(TCodec.tc2 tcn__CatSim "A'6'U0y8%211%411&S2r1%211&S3(4r2(8%118%43931%611p081pW<<1").
Proof. intros b H. apply Forall_cons; [exact H | apply Forall_nil]. Qed.
Lemma buf_modeled_nil : ltac2:(TCodec.tc2 tcn__CatSim "7&S2(8'U0y8%211%411%611").
Proof. unfold buf_modeled. cbn. unfold rw_bytes_max. lia. Qed.
Lemma buf_modeled_skipn : ltac2:(TCodec.tc2 tcn__CatSim "A'7'6'U0y8%211%411&S2r1%211&Er3r2%33821%711p061pW<:1pXL@1").
Proof.
intros n b H. unfold buf_modeled in *. rewrite length_skipn. lia.
Qed.
Lemma write1_check_n : ltac2:(TCodec.tc2 tcn__CatSim "S<'6'Q1%211'Q;'U0yR0%211'R7y8%511%:11'7&S4r3%211'='G&U1r5%22>1+R0%63521&Q<r7(1%3221&TO+1%22G1%>3G41'9%11E&Q>r8u1%=221u2%?241%63531(2%12NF%J3:31&S2r6%211'A%12<3&5%12Q7?%42J1'O&M&R2r=r<r;%43321&RM%Q424Q2%211%Q626J%Q727I&RK(4';%12QKQF(:%14QMQH7Q2(8%114%73531(RH&L&Cr9%23R2Q:1%42R31%=2R7R3%:11%?2R9R9%<11'R6%>11%<675331>%F2>1r:%Q36NKJI21(N&D'R;(R:%11QO%44RC31A%6281%R?3Q<81p0Q>1p0QB1p0QE1p0QI1p0R61p0R?1p0RG1pXLRK1pW@RM1pXBS11pZ:S31pXFS71pYHS91").
Proof.
intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
unfold check_write.
rewrite Hg; norm_fd32; rewrite Hfd.
change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
rewrite Hmc. cbv beta iota.
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc. cbv beta iota. cbv zeta.
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
by (rewrite length_firstn; lia).
assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
{ rewrite (len_word_unsigned (firstn n buf));
[exact Hlenf | rewrite Hlenf; lia]. }
rewrite ?Hru.
assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
by (apply Z.leb_le; lia).
rewrite ?Hg1, ?Hg2. cbn [andb].
rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.
Lemma write1_ok_n : ltac2:(TCodec.tc2 tcn__CatSim "S7'6'Q1%211'Q;'U0yR0%211'R7y8%511%:11'7&S4r3%211'='G&U1r5%22>1+R0%63521&Q<r7(1%3221&TO+1%22G1%>3G41'9%11E&Q>r8u1%=221u2%?241%63531(2%12NF%J3:31&S2r6%211'A%12<3&5%12Q7?%42J1&R3&R2r=r<r;%43321r:(Q3'R9&RK(4';%12QHQC(:%Q:2;N%24QKQF1Q0(8%115%83631(RH&L&Cr9%23R0Q81%42R11%>2R5R1%:11%@2R7R7%<11'R6%>11%<675331>%G2>1&D'R;(R:%11QJ%44R>31>%O4N6Q01%Q73Q2Q11p0Q91p0Q=1p0Q@1p0QD1p0R11p0R:1p0RB1pXLRF1pW@RH1pXBRL1pZ:RN1pXFS21pYHS41").
Proof.
intros segs ms x8 model buf n Hfd Hno Hg Hr Hcnt Hn1 Hn2.
apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.
Lemma write1_ok_inv : ltac2:(TCodec.tc2 tcn__CatSim "SE'6'Q1%211'Q;'U0yR0%211'R7'R9'R;%:11y8%811%=11&S4r5%211'='G&U1r7%22@1+R0%63521&Q<r9(1%3221&TO+1%22I1%>3I41'9%11D&Q>r:u1%=221u2%?241%63531(2r4%22N1%K3;41'A&5%12Q3Q0%32<1&R3&R2r=r<r;%43321(Q3r8%24QAQ01Q5%934G1'>'7'<r1%B2K1%B2QD8%D231&RK(4';%12QO9(:r>%Q@21Q4%34R3=1;(8%116%93731(RH&L&C%13R4BH%32R51%>2R<R5%911%@2R>R>%;11'R6%=11%;675331=%G2=1%R93RBQ51%R:3RDQHQ7&D(R:%11R0%34RCRF1?%R?3RFR71%Q4261%Q5281%Q62Q21%Q72Q51qXLQ91%Q;2Q:1p0Q=1p0QH1p0QM1p0R;1p0RD1p0RL1pW@S01pX2S41pXDS81pX0S81pXBS:1pZ:S<1pXFS@1pYHSB1").
Proof.
intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hnb Hspec.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply check_write_complete_ok in Hspec.
unfold check_write in Hspec.
rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
cbv beta iota in Hspec; [discriminate|].
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
assert (Hcpos : (1 <= c)%nat)
by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
by apply length_firstn.
assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
by (rewrite Hfl; apply Nat.eqb_neq; lia).
rewrite Hg0 in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?]; try discriminate.
destruct ((1 <=? bv_unsigned ret)%Z
&& (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
[|discriminate].
destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
eqn:Hreads; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in Hgr as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite Hfl in H2.
apply access_ranges_eqb_eq in Hreads. subst copyins.
exists (Z.to_nat (bv_unsigned ret)).
assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
= firstn (Z.to_nat (bv_unsigned ret)) buf)
by (rewrite firstn_firstn; f_equal; lia).
rewrite Hff.
assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
by (apply len_word_firstn_ret; lia).
rewrite Hlw. repeat split; try reflexivity; lia.
Qed.
Lemma write1_no_unmodeled : ltac2:(TCodec.tc2 tcn__CatSim "R8'6'Q1%211'Q;'U0yR0%211'R7y8%511%:11&S4r2%211'='G&U1r4%22=1+R0%63521&Q<r6(1%3221&TO+1%22F1%>3F41'9%11D&Q>r7u1%=221u2%?241%63531(2%12MF%J3:31&S2r5%211'A&5%12Q5H%32>1&@&R3&R2r;r:r9%43321r8(Q4'R9%211%:3541%<11p0>1p0C1p0G1p0Q41p0Q=1p0QE1pW@QI1pXBQM1pZ:QO1pXFR31pYHR51").
Proof.
intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
unfold fd1chan in Hfd.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_write in Hspec.
rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
rewrite Hmc in Hspec. cbv beta iota in Hspec.
destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
{ exfalso.
assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
congruence. }
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
in Hspec.
destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
discriminate Hspec.
Qed.
Lemma is_prefix_app_mono {A} : forall (l a b : list A),
is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.
Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
end.
Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
(1 <= n)%nat -> (n <= length buf)%nat ->
wpick ch bufs tr ->
wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).
Lemma wpick_wevents : ltac2:(TCodec.tc2 tcn__CatSim "J'U0yR0%211'6y8%511%311%411'B'Au1&5r1%2281%5241qW<91%83:14'S<r3r2&S:%1232%53431p071pWBA1pWHG1").
Proof.
intros ch bufs H; induction H as [|b bs Hb Hbs IH].
- apply wp_nil.
- cbn [wevents_ch].
pose proof (wp_cons ch b bs (length b) _ Hb (Nat.le_refl _) IH) as Hc.
rewrite firstn_all in Hc. exact Hc.
Qed.
Section WithSegs.
Variable segs : list Segment.
Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = Z_to_bv 64 1 ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit ms' bufs code ->
to_wexit ms bufs code.
Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
msteps ms' ms'' ->
msteps ms ms''.
Lemma msteps_one : ltac2:(TCodec.tc2 tcn__CatSim "M'Q;'='9'U0yR0%211%411&Q@r2%211(0%116%;3631'Q:%11>&QBvTKr3%3221(Q9%12D<%D3731'RNr4%2217p041p0>1pXHK1pXFL1").
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.
Lemma msteps_trans : ltac2:(TCodec.tc2 tcn__CatSim "<'Q;'RNr3r2%3221r5%5214p031p041pXJ91pXH:1pXF;1").
Proof.
intros ms ms' ms'' H; induction H; [auto|].
intro H2. eapply mst_step; eauto.
Qed.
Lemma msteps_to_wexit : ltac2:(TCodec.tc2 tcn__CatSim "H'Q;'6'U0y8%211%411%511yR0%611'RNr4r3%3221'ROr2%23541r6%43176p031p071pWJ<1pWB?1pXHF1pXFG1").
Proof.
intros ms ms' bufs code H; induction H; [auto|].
intro Hw. eapply tw_step; eauto.
Qed.
Lemma to_wexit_bufs_nonempty : ltac2:(TCodec.tc2 tcn__CatSim "J'Q;'6'U0y8%211%411%511yR0%611'ROr3r2r1%43321'B'Au1&5%12>6%4231qW<?1%73@1;p091pWJ?1pWBB1pXFI1").
Proof.
intros ms bufs code H;
induction H as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH].
- constructor.
- constructor; [exact Hnb | apply (IH (length buf)); lia].
- exact IH.
Qed.
Lemma sstep_write_next_inv : ltac2:(TCodec.tc2 tcn__CatSim "SI'Q;'R7'U0yR0%211'6y8%511%311'R;%511'QF'='9%11:&RFr5%211(0%11?%83631';%12BB%B11&RGr6%211(8%116%A3631&S4r7%211&Q@r9%211(2%12Q16%J3H31'G&U1r8%22Q71+R0%Q03521&Q<r;(1%3221&TO+1%22Q@1%Q83Q@41%Q81Q=&Q>r<u1%<221u2%>241%63531%I2QEK%QB3921'A&5r:%22QK1%42;1'QOvTK(QJr>r=%3221(QC%11Q9%8473;1'>'7'<r1%B2I1%B2R;:%D231&D(R:%11Q3&C%13RA8@%54RBR@31%R>3R@Q31&QD&QAr@&L%12RH7%4231%611r?%M221%RH3RIQF1%F2;1%G2C1%H2F1qXLJ1%L2K1p0N1p0Q81p0Q>1p0QI1p0R21p0R91p0R@1p0RD1p0RN1pWFS81pX2S:1pW@S=1pZ:SB1pXBSF1pXFSH1").
Proof.
intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
subst eff model' evs0; exists n
end.
match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
rewrite apply_effect_copyins_no_write. repeat split; auto.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
discriminate
end.
Qed.
Lemma sstep_write_inv : ltac2:(TCodec.tc2 tcn__CatSim "SM'Q;'R7'U0yR0%211'6y8%511%311'R;%511'R1'='9%11:&RFr5%211(0%11?%83631';%12BB%B11&RGr6%211(8%116%A3631&S4r7%211&Q@r9%211(2%12Q16%J3H31'G&U1r8%22Q71+R0%Q03521&Q<r;(1%3221&TO+1%22Q@1%Q83Q@41%Q81Q=&Q>r<u1%<221u2%>241%63531%I2QEK%QB3921&S2r:%211'A&5%12QMF%32=1'QOvTK(QJr?r>%3221%6451N<'>'7'<r1%?2I1%?2R;8%A231r=&D(R:%11Q4&C%13RB9?%54RCRA31%R?3RA71(QC&QD&QArA&L%12RJ8%4231%611r@%M221%:11%RK3RLQ@1%I2=1%J2F1%K2I1qXLM1%O2N1p0Q11p0Q91p0Q>1p0QB1p0QM1p0R61p0R=1p0RD1p0RH1p0S21pYNS<1pX2S>1pW@SA1pZ:SF1pXBSJ1pXFSL1").
Proof.
intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
destruct st as [c'|].
- destruct (sstep_write_next_inv ms model x8 buf evs c'
Hh Hlazy Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
-
exfalso. inversion Hss; subst; try congruence.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
discriminate
end.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
end.
Qed.
Fixpoint wevents (bufs : list (list byte)) : list event :=
match bufs with
| [] => []
| buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
end.
Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
fun tr o =>
(exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
/\ exits_with code tr o.
Lemma to_wexit_exec : ltac2:(TCodec.tc2 tcn__CatSim "QI'Q;'6'U0y8%211%411%511yR0%611'ROr3r2r1%43321'R7'='9%119&RF%117(0%11=%73531';%12@@%H11&RG%11@(8%115%?3531&S4%11F&S3r7%211'Q6vTK(QJr9r5%3221&S0r8&RE%115%433<1%;3:61p0=1p0A1p0D1p0M1pXBQ61p0Q81pWJQ>1pWBQA1pXFQH1").
Proof.
intros ms bufs code Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model Hh Hlazy Hfd Hbm.
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
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* unfold wexit_post. cbn beta. rewrite app_nil_r. split.
-- exists []. split; [apply wp_nil | reflexivity].
-- cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
-
apply Forall_cons_iff in Hbm as [Hb Hbs].
apply exec_step; [exact Hh | | |].
+
eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length buf)]
(mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
* exact Hh.
* exact Hsvc.
* apply write1_ok_n; try assumption. apply Nat.le_refl.
* exact Hh.
* rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+ intros evs Hss.
destruct (sstep_write_inv ms model x8 buf evs SError
Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & _ & _ & _ & Habs).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_write_inv ms model x8 buf evs (SNext c')
Hh Hlazy Hfd Hsvc Hno Hg Hr Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
injection Hc' as ->.
eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy Hfd Hbs) |].
intros tr o ((full & Hpick & ->) & Hx). split.
* exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
split; [apply wp_cons; assumption | apply app_assoc].
* exact Hx.
-
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_wexit_star_admits : ltac2:(TCodec.tc2 tcn__CatSim "R>'Q;'6'U0y8%211%411%511yR0%611'ROr3r2r1%43321'R7'R;%?11'='9%11;&RF%11:(0%11?%73531';%12BB%J11&RG%11C(8%115%?3531&S4r4%211&S3r8%211'S<&TO+1%22Q31r9r5%63321'>'QF'R0vTK(QJr<%221?&3r7(4(R5r:&RE%11F%4231%O1Q>%73Q?21%:3Q@91%@4?<1QDqWDB1%D2C1p0F1p0N1p0Q21p0Q61p0Q?1pX6QH1pXBQK1p0QM1pWJR31pWBR61pXFR=1").
Proof.
intros ms bufs code Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH];
intros model full Hh Hlazy Hfd Hbm Hpick.
-
inversion Hpick; subst. cbn [app].
exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
apply star_one.
replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
+ exact Hh.
+ exact Hsvc.
+ apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
+ cbn. reflexivity.
+ apply m_killed_with_halted.
-
apply Forall_cons_iff in Hbm as [Hb Hbs].
inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
destruct (IH n Hn1 Hn2 model tr Hh Hlazy Hfd Hbs Hpick') as [c Hstar].
exists c. rewrite <- app_assoc.
eapply star_step; [| exact Hstar].
rewrite <- (apply_effect_copyins_no_write ms
(len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model model
(map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
-
destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
exists c.
replace (full ++ [ExitEv code (m_fs model)])
with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_wexit_star_only : ltac2:(TCodec.tc2 tcn__CatSim "RA'Q;'6'U0y8%211%411%511yR0%611'ROr3r2r1%43321'R7'='9%119&RF%117(0%11=%73531';%12@@%H11&RG%11@(8%115%?3531&S4%11F&S3r7%211'R;%Q411'QF'R0vTK(QJr;%2219%5441Q1Q0'>'<'S<&TO+1%22Q;1r<%5321Q8&QIr4&3(4(R5&REr9%211%42C1%Q21J%73K21%93LQD1%<3M;1%D2>1qX6N1%G2O1p0I1pWDQ01pZ8Q21p0Q51p0Q91p0Q<1p0QE1pXBQN1p0R01pWJR61pWBR91pXFR@1").
Proof.
intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
as (tr' & o & _ & HQ).
unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_wexit_no_error : ltac2:(TCodec.tc2 tcn__CatSim "QG'Q;'R7'6'U0y8%211%411%511yR0%611'='9%113&RFr3%211(0%118%83631';%12;;%C11&RGr4%211(8%116%A3631&S4r5%211'ROr7%2314:&S3r6%211&@&QMvTK(QJr9r8%3221%6251%811p0:1p0>1p0B1p0F1p0Q01pWJQ:1pWBQ=1pXBQD1pXFQF1").
Proof.
intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
End WithSegs.
Lemma init_model_fd1chan : ltac2:(TCodec.tc2 tcn__CatSim "I'6';'U0yR0%211%4211%611'G'R8&S4&RDr6r5r4r3r2r1%76654321%911pX8;1pX>=1pYLA1pX@B1pW>C1pY8B1").
Proof. reflexivity. Qed.
Lemma cat_omni_run_te : ltac2:(TCodec.tc2 tcn__CatSim "R1'6'Q1%211'F'Q0'U0yR0%211'R4'G'R8y8%711%=11%>11'S7r;&QHr:r9r8r5&R=r3%211&R>%113&RC%115&R@%117%>9?=<;:7531r2r1%C4B321&S3%11=&Q8(Q2r=r<%3321Ir6(QKr7%24KJI1&S;r4&R?%11L%433K1%>5:96N1p0@1p0C1pWJQ?1pWBQ91pX8Q>1pX>Q@1pY>QB1pX@QD1pW>QE1pYLQF1pY2QJ1pY0QL1pYHQN1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm.
cbn [omni_run]. unfold init_config.
exact (to_wexit_exec segs _ bufs code Hte
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl eq_refl Hbm).
Qed.
Lemma cat_obs_iff_te : ltac2:(TCodec.tc2 tcn__CatSim "RF'6'Q1%211'F'Q0'U0yR0%211'R4'G'R8y8%711%=11%>11'S7r;&QHr:r9r8r5&R=r3%211&R>%113&RC%115&R@%117%>9?=<;:7531r2r1%C4B321&S3%11='R;%Q611&?&QLr>&QGr=r<r7r6%59643OMLK21%8371?'>'<'S<&TO+1%22Q@1%4319F&QI&3(4(R5&R?%11@%32Q91(8%11K%73L31%93MQ11%;3NQ31%B2=1qX6O1%E2Q01%Q02G1pZ8Q21p0Q51p0Q81pWJR41pWBQN1pX8R31pX>R51pY>R71pX@R91pW>R:1pYLR;1pY2R?1pY0RA1pYHRC1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm tr.
set (fs0 := in_fs inp) in *.
unfold init_config in *.
set (ms := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
assert (Hh : m_halted (init_model (segments_reserved segs) brk0 mb sp lim inp) = None) by reflexivity.
assert (Hlazy : m_vm_lazy (init_model (segments_reserved segs) brk0 mb sp lim inp) = []) by reflexivity.
assert (Hfd : fd1chan (init_model (segments_reserved segs) brk0 mb sp lim inp)) by reflexivity.
assert (Hfs : m_fs (init_model (segments_reserved segs) brk0 mb sp lim inp) = fs0) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (to_wexit_star_only segs ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
as (full & Hw & Hpref).
rewrite Hfs in Hpref.
exists full. split; [exact Hw|].
eapply is_prefix_trans; eauto.
- intros (full & Hw & Hp).
destruct (to_wexit_star_admits segs ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
as [c Hstar].
rewrite Hfs in Hstar.
exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.
Lemma cat_no_error_run_te : ltac2:(TCodec.tc2 tcn__CatSim "QL'6'Q1%211'F'Q0'U0yR0%211'R4'G'R8y8%711%=11%>11'S7r;&QHr:r9r8r5&R=r3%211&R>%113&RC%115&R@%117%>9?=<;:7531r2r1%C4B321&S3%11=&@&QMr=&QGr<r7r6%4953LJIH21G%7261%911p0;1p0>1pWJQ:1pWBQ41pX8Q91pX>Q;1pY>Q=1pX@Q?1pW>Q@1pYLQA1pY2QE1pY0QG1pYHQI1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply exec_no_error.
eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma cat_must_exit_with_te : ltac2:(TCodec.tc2 tcn__CatSim "QL'6'Q1%211'F'Q0'U0yR0%211'R4'G'R8y8%711%=11%>11'S7r;&QHr:r9r8r5&R=r3%211&R>%113&RC%115&R@%117%>9?=<;:7531r2r1%C4B321&S3%11=&J(Q2r=r<%3321Ir6(QKr7%24KJI1%95G541Ip0;1p0>1pWJQ:1pWBQ41pX8Q91pX>Q;1pY>Q=1pX@Q?1pW>Q@1pYLQA1pY2QE1pY0QG1pYHQI1").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm. apply must_exit_with_iff.
eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) |].
intros tr o (_ & Hx). exact Hx.
Qed.
Lemma cat_omni_run_te_code_unique : ltac2:(TCodec.tc2 tcn__CatSim "R3'6'Q1%211'F'Q0'U0yR0%211'R4'G'R8y8%711%=11%>11'S7r<&QHr;r:r9r6&R=r4%211&R>%113&RC%115&R@%117%>9?=<;:7531r3r2%C4B321&S3%11=&Q8(Q2r>r=%3321Ir7(QKr8%24KJI1&Q7%11?%;5763K1'=r5%23Q<L1p041p0A1p0D1pWLQ@1pWJQA1pWBQ;1pX8Q@1pX>QB1pY>QD1pX@QF1pW>QG1pYLQH1pY2QL1pY0QN1pYHR01").
Proof.
intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hex.
pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm) as Hrun.
cbn [omni_run] in Hrun, Hex.
destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.
Lemma cat_omni_strong_equiv_te : ltac2:(TCodec.tc2 tcn__CatSim "RA'6'Q1%211'F'Q0'U0yR0%211'R4y8%511%;11%<11'R8'S7rA&QHr@r?r>r;&R=r1%211&R>%113&RC%115&R@%117%>9?=<;:7531r3r2%C4B321r:r9r8r5%A16%?17%>18%=19%J9F87654321r4%N4H21=&S3%119&K(Q2rDrCrB%43321r=r<%7321Q3(QK%14Q:Q8Q7Q6r7%34IHG1%=58531Ap0?1p0B1p0N1pX8QC1pWJQJ1pWBQF1pW8QK1pW2QM1pVNQN1pW:QO1pW6R31pW4R51pZ6R71pYDR21pY<R41pY6R51pYFR61pYBR:1pY@R<1pYJR>1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
Hsource Htarget Hbm.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm tr).
rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm).
Qed.
Lemma cat_strong_equiv_te : ltac2:(TCodec.tc2 tcn__CatSim "RN'6'Q1%211'F'Q0'U0yR0%211'R4'Gy8%611%<11%=11'R8'S7rC&QHrBrAr@r=&R=r1%211&R>%113&RC%115&R@%117%>9?=<;:7531r3r2%C4B321r<r;r:r9r6%B17%@18%?19%>1:%K9987654321r4%O4;21>&S3r5%211'<&I&QN(Q2rFrErD%43321r?(QK%14Q<Q:Q9Q8%94431@%;11&Hr>%<31Q<Nr7r8%94Q0ON1%A4431H%7291%E291p0G1p0K1p0Q81pX8QM1pWJR51pWBR01pW0R51pW8R71pW2R91pVNR:1pW:R;1pW6R?1pW4RA1pZ6RC1pY:R=1pYDR?1pY<RA1pY6RB1pYFRC1pYBRG1pY@RI1pYJRK1").
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp Hsource Htarget Hbm.
split.
{ apply no_error_run_modeled.
apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm). }
right. split.
- intro tr. cbn.
rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm tr).
rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm tr).
reflexivity.
- cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm).
Qed.
Definition fdchan (fd ch : word) (model : Model) : Prop :=
fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false.
Lemma fd1chan_fdchan : ltac2:(TCodec.tc2 tcn__CatSim "='R7&S4r1%211&S5&TOyR0+1%3221r2%63221p081pXB<1").
Proof.
intros model H. split; [exact H | reflexivity].
Qed.
Lemma init_model_fdchan2 : ltac2:(TCodec.tc2 tcn__CatSim "L'6';'U0yR0%211%4211%611'G'R8&S5&TO+2%2291&RDr6r5r4r3r2r1%76654321%<3991pX8>1pX>@1pYLD1pX@E1pW>F1pY8E1").
Proof. intros. split; reflexivity. Qed.
Lemma write_ch_check_n : ltac2:(TCodec.tc2 tcn__CatSim "SA'6'Q1%211'Q;'U0yR0%211'R7y8%511%:11'7&S5r4r3r5%43321'=&RM%114%33>15'G&U1r8%22C1+R0%93521&Q<r:(1%3221r7%?3J21'9%11H&Q>r;u1%;221u2%=241%63531(2r6%22Q21%L3;41&S2%11@'A%12<B&5r9%22Q;1%52N1'O&M&R2r@r?r>%43321%Q223Q0%Q<11%Q425J%Q526I&RK(4';%12QNQI(:%14R0QK7C(8%114%73531(RH&L&C%13R4JQA%32R51%<2R9R5%911%>2R;R;%;11'R6%=11%;675331=%E2=1r=%Q16LJIH21(N&D'R;(R:%11QI%44RE31A%6281%R?3Q:81p0Q<1p0QA1p0QD1p0QG1p0R51p0R<1p0RC1p0RH1pXLRN1pW@S01pWHS51pX4S61pXBS61pZ:S81pXFS<1pYHS>1").
Proof.
intros segs ms x8 model fd ch buf n [Hfd Hch] H32 Hno Hg Hr Hcnt Hn1 Hn2.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
unfold check_write.
rewrite Hg, H32, Hfd, Hch. cbv beta iota.
rewrite Hmc. cbv beta iota.
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc. cbv beta iota. cbv zeta.
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
by (rewrite length_firstn; lia).
assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
{ rewrite (len_word_unsigned (firstn n buf));
[exact Hlenf | rewrite Hlenf; lia]. }
rewrite ?Hru.
assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
by (apply Z.leb_le; lia).
rewrite ?Hg1, ?Hg2. cbn [andb].
rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.
Lemma write_ch_ok_n : ltac2:(TCodec.tc2 tcn__CatSim "S='6'Q1%211'Q;'U0yR0%211'R7y8%511%:11'7&S5r4r3r5%43321'=&RM%114%33>15'G&U1r8%22C1+R0%93521&Q<r:(1%3221r7%?3J21'9%11H&Q>r;u1%;221u2%=241%63531(2r6%22Q21%L3;41&S2%11@'A%12<B&5r9%22Q;1%52N1&R3&R2r@r?r>%43321r=(Q3'R9&RK(4';%12QLQG(:%Q92;O%24QOQJ1B(8%115%83631(RH&L&C%13R3IQ@%32R41%=2R8R4%911%?2R:R:%;11'R6%=11%;675331=%F2=1&D'R;(R:%11QE%44RA31>%N4M6O1%Q63Q1Q01p0Q81p0Q=1p0Q@1p0QC1p0R11p0R81p0R?1p0RD1pXLRJ1pW@RL1pWHS11pX4S21pXBS21pZ:S41pXFS81pYHS:1").
Proof.
intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hcnt Hn1 Hn2.
apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.
Lemma write_ch_ok_inv : ltac2:(TCodec.tc2 tcn__CatSim "SK'6'Q1%211'Q;'U0yR0%211'R7'R9'R;%:11y8%811%=11&S5r6r5r7%43321'=&RM%114%33@15'G&U1r:%22E1+R0%93521&Q<r<(1%3221r9%?3L21'9%11G&Q>r=u1%;221u2%=241%63531(2%12Q0M%K3:31'A&5%12Q5Q2%32;1&R3&R2r@r?r>%43321(Q3r8%24QCQ2J1%934F1'>'7'<r1%B2J1%B2QFQ1%D231&RK(4';%12R19(:rA%Q=21Q3%34R5=1;(8%116%93731(RH&L&C%13R6BQA%32R71%>2R>R7%911%@2R@R@%;11'R6%=11%;675331=%G2=1%R93RDQN1r;%R;3RG1Q8&D(R:%11QK%34RFRI1@%R@3RIR:1%Q5261%Q6291%Q72Q31%Q82Q61qXLQ:1%Q<2Q;1p0Q>1p0QI1p0QN1p0R;1p0RB1p0RI1p0RN1pW@S41pX2S81pXDS<1pX0S<1pWHS?1pX4S@1pXBS@1pZ:SB1pXFSF1pYHSH1").
Proof.
intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hnb Hspec.
destruct Hfdc as [Hfd Hch].
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply check_write_complete_ok in Hspec.
unfold check_write in Hspec.
rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
cbv beta iota in Hspec; [discriminate|].
assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
assert (Hcpos : (1 <= c)%nat)
by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
by apply length_firstn.
assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
by (rewrite Hfl; apply Nat.eqb_neq; lia).
rewrite Hg0 in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
destruct zs as [|? ?]; destruct us as [|? ?];
destruct cs as [|? ?]; try discriminate.
destruct ((1 <=? bv_unsigned ret)%Z
&& (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
[|discriminate].
destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
eqn:Hreads; [|discriminate].
inversion Hspec; clear Hspec; subst.
apply andb_true_iff in Hgr as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
rewrite Hfl in H2.
apply access_ranges_eqb_eq in Hreads. subst copyins.
exists (Z.to_nat (bv_unsigned ret)).
assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
= firstn (Z.to_nat (bv_unsigned ret)) buf)
by (rewrite firstn_firstn; f_equal; lia).
rewrite Hff.
assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
by (apply len_word_firstn_ret; lia).
rewrite Hlw. repeat split; try reflexivity; lia.
Qed.
Lemma write_ch_no_unmodeled : ltac2:(TCodec.tc2 tcn__CatSim "R>'6'Q1%211'Q;'U0yR0%211'R7y8%511%:11&S5r3r2r4%43321'=&RM%114%33=15'G&U1r7%22B1+R0%93521&Q<r9(1%3221r6%?3I21'9%11G&Q>r:u1%;221u2%=241%63531(2r5%22Q11%L3;41&S2%11@'A&5%12Q8K%32>1&@&R3&R2r>r=r<%43321r;(Q4'R9%211%:3541%<11p0>1p0C1p0F1p0Q41p0Q;1p0QB1p0QG1pW@QM1pWHR21pX4R31pXBR31pZ:R51pXFR91pYHR;1").
Proof.
intros segs ms x8 model fd ch buf [Hfd Hch] H32 Hno Hg Hr Hcnt Hnb Hspec.
assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
(ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
{ rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
by (unfold buf_modeled in Hcnt; lia).
assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
by (apply rw_range_in_range; exact Hcw).
apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_write in Hspec.
rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
rewrite Hmc in Hspec. cbv beta iota in Hspec.
destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
{ exfalso.
assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
congruence. }
rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
in Hspec.
destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
discriminate Hspec.
Qed.
Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
(1 <= length buf)%nat ->
(forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wexit_ch ms' bufs code ->
to_wexit_ch ms bufs code.
Lemma msteps_to_wexit_ch : ltac2:(TCodec.tc2 tcn__CatSim "I'Q;'6'U0y8%211%411%511yR0%611'S6vTKr4r3%43321'S1r2%23541r6%43176p031p071pWJ=1pWB@1pXHG1pXFH1").
Proof.
intros ms ms' bufs code H; induction H; [auto|].
intro Hw. eapply twc_step; eauto.
Qed.
Hypothesis Hfd32 : fd32 fd = fd.
Lemma sstep_write_ch_inv : ltac2:(TCodec.tc2 tcn__CatSim "SL'Q;'R7'U0yR0%211'6y8%511%311'R;%511'R1'='9%11:&RFr5%211(0%11?%83631';%12BB%B11&RGr6%211(8%116%A3631&S5vT1vSKr7%43321&Q@r9%211(2%12Q36%L3J31'G&U1r8%22Q91+R0%Q23521&Q<r;(1%3221%Q73Q?1D%Q71Q<&Q>r<u1%9221u2%;241%63531%F2QDH%QA3921&S2r:%211'A&5%12QLC%32=1'QOvTK(QJr?r>%3221%6451K<'>'7'<r1%?2I1%?2R:8%A231r=&D(R:%11QF&C%13RA9?%54RBR@31%R>3R@71(QC&QD&QArA&L%12RI8%4231%611r@%M221%:11%RJ3RKQ@1%I2=1%J2F1%K2I1qXLM1%O2N1p0Q11p0Q91p0Q>1p0QB1p0QM1p0R31p0R:1p0RA1p0RG1p0S11pYNS;1pX2S=1pW@S@1pZ:SE1pXBSI1pXFSK1").
Proof.
intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hcnt Hnb Hss.
revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
- match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
subst eff model' evs0; exists n
end.
match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
rewrite apply_effect_copyins_no_write. repeat split; auto.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
discriminate
end.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite Hh in H6; discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
discriminate
end.
- exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
end.
Qed.
End WithSegsCh.
Lemma to_wexit_ch_1 : ltac2:(TCodec.tc2 tcn__CatSim "L'6'Q1%211'Q;'U0y8%211%711%811yR0%611'S7r4r3r2r1%544321'S8r5&TO+1%22<1%5541:98p071pWJ>1pWBA1pXFG1pYHI1").
Proof.
intros segs ms bufs code H; induction H.
- eapply twc_exit; eassumption.
- eapply twc_write; eassumption.
- eapply twc_step; eassumption.
Qed.
Lemma wevents_ch_1 : ltac2:(TCodec.tc2 tcn__CatSim "D'6'U0y8%211%411%511'='R;%811&S:&TOyR0+1%3221r1%6221&S9%113%<3:31pWB>1").
Proof.
induction bufs as [|b bs IH]; cbn [wevents_ch wevents]; [reflexivity|].
rewrite IH. reflexivity.
Qed.
