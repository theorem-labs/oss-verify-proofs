(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Scfg () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mremap."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Scfg.WithSegs."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1list"; "1negb"; "1nil"; "1option"; "1true"; "2and"; "2eq"; "2not"; "2or"]; ["3Z"; "4Ok"; "5machine_state"; "5ms_svc_pending"; "6FamAlloc"; "6FamFs"; "6InjectedArm"; "6SError"; "6SNext"; "6SpuriousCfg"; "6brk_refusal_b"; "6cfg_model"; "6cfg_ms"; "6config"; "6family_may_fail"; "6ia_errnos"]; ["6ia_family"; "6injected_arm"; "6injected_family_off"; "6mkCfg"; "6mkInjectedArm"; "6obs_trace_cfg"; "6reaches_error_cfg"; "6refusal_b"; "6ret_in_errnos"; "6sc_alloc"; "6sc_fs"; "6spurious_refusal_cfg"; "6sstep"; "6sstep_cfg"; "6star_cfg"; "6step_to"]; ["7syscall_spec"; "8ENOMEM"; "8Model"; "8SyscallEffect"; "8SyscallInput"; "8eff_ret"; "8errno_ret"; "8event"; "8in_arg"; "8in_sysno"; "8m_halted"; "9openat_errnos"; ":mmap_errnos"; ";mprotect_errnos"; "<mremap_errnos"; "=bv_eqb"]; [">fam_on"; "0a"; "0c"; "0c'"; "0c0"; "0c1"; "0c2"; "0c3"; "0cfg"; "0e"; "0eff"; "0eff'"; "0eff1"; "0evs"; "0evs'"; "0evs1"]; ["0i"; "0m"; "0m'"; "0m1"; "0model"; "0ms"; "0n"; "0r"; "0scfg"; "0segs"; "0st"; "?bv"; "?bv_unsigned"; "0tr"; "0tr1"; "0tr2"]; ["0x8"]]).
Lemma injected_arm_214 : ltac2:(TCodec.tc2 tcn__Scfg "@'=':'F%211&Q1+VF%211(2(Q4(D(9'@%211%53841%72<1%?3<91").
Proof. reflexivity. Qed.
Lemma injected_arm_216 : ltac2:(TCodec.tc2 tcn__Scfg ">'=':'F%211&Q1+VH%211(2(Q4(D&QN%33621%52:1%=3:71").
Proof. reflexivity. Qed.
Lemma injected_arm_222 : ltac2:(TCodec.tc2 tcn__Scfg ">'=':'F%211&Q1+VN%211(2(Q4(D&QL%33621%52:1%=3:71").
Proof. reflexivity. Qed.
Lemma injected_arm_226 : ltac2:(TCodec.tc2 tcn__Scfg ">'=':'F%211&Q1+W2%211(2(Q4(D&QM%33621%52:1%=3:71").
Proof. reflexivity. Qed.
Lemma injected_arm_56 : ltac2:(TCodec.tc2 tcn__Scfg ">'=':'F%211&Q1+QH%211(2(Q4(E&QK%33621%52:1%=3:71").
Proof. reflexivity. Qed.
Lemma injected_arm_29 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+M%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_57 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+QI%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_63 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+QO%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_64 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+R0%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_66 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+R2%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_93 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+RM%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_94 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+RN%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_96 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+S0%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma injected_arm_215 : ltac2:(TCodec.tc2 tcn__Scfg ":'=':'F%211&Q1+VG%211(0%116%93631"). Proof. reflexivity. Qed.
Lemma ret_in_errnos_1 : ltac2:(TCodec.tc2 tcn__Scfg "E'@'RKyR0%211'='4&Q8(5r2(9%11:%43;31r1%7221&QO&QF%118%33?51%>3=51pU@@1pTDD1").
Proof. intros e r. unfold ret_in_errnos. cbn [existsb]. apply orb_false_r. Qed.
Lemma ret_in_errnos_nil : ltac2:(TCodec.tc2 tcn__Scfg ">'RKyR0%211'='4&Q8(9'@%211r1%5221(6%93821pU@;1").
Proof. reflexivity. Qed.
Lemma injected_family_off_none : ltac2:(TCodec.tc2 tcn__Scfg "K'I'QD'=':'F%211&Q1&RLyR0&QIr1%211%5241%711(0%11;%>3;31'4&Q2r3r2%3221(6%E3621p081pU2H1pTBJ1").
Proof. intros cfg i H. unfold injected_family_off. rewrite H. reflexivity. Qed.
Lemma injected_family_off_some : ltac2:(TCodec.tc2 tcn__Scfg "Q2'I'QD'F'=':%113&Q1&RLyR0&QIr2%211%5241%711(2r1%22>1%>3<41'4&Q2r4r3%3221&8&N&Q0%11@%3271%511%J3;71p0=1pT4M1pU2O1pTBQ11").
Proof. intros cfg i a H. unfold injected_family_off. rewrite H. reflexivity. Qed.
Lemma refusal_b_none : ltac2:(TCodec.tc2 tcn__Scfg "N'QD'QB'RKyR0%211'=':'F%211&Q1&RL&QIr3%211%42;1%611(0%11:%=3:31'4&Q7r4r2%332;1(6%D3621p081pU@G1pU4K1pU2M1").
Proof.
intros i m r H. unfold refusal_b.
destruct (Z.eqb (bv_unsigned (in_sysno i)) 214) eqn:E.
- apply Z.eqb_eq in E. rewrite E in H. rewrite injected_arm_214 in H. discriminate H.
- rewrite H. reflexivity.
Qed.
Lemma refusal_b_errnos : ltac2:(TCodec.tc2 tcn__Scfg "Q<'QD'QB'RKyR0%211'F&>'='@&RL&QIr4%211%42:1+VF%83721%:11':%11=&Q1r5%;11%=2C1%411(2r2%22E1%D3941'4&Q7r6%231;D&Q8&Or3%211%421I%N3961p0;1p0G1pT4Q31pU@Q51pU4Q91pU2Q;1").
Proof.
intros i m r a Hne H. unfold refusal_b.
destruct (Z.eqb (bv_unsigned (in_sysno i)) 214) eqn:E.
- apply Z.eqb_eq in E. contradiction.
- rewrite H. reflexivity.
Qed.
Lemma refusal_b_brk : ltac2:(TCodec.tc2 tcn__Scfg "M'QD'QB'RKyR0%211'='@&RL&QIr3%211%4281+VF%83721'4&Q7r4r2%33291&J&QH(1%2261%43>16%C3:61p0<1pU@F1pU4J1pU2L1").
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.
Lemma refusal_b_mmap : ltac2:(TCodec.tc2 tcn__Scfg "M'QD'QB'RKyR0%211'='@&RL&QIr3%211%4281+VN%83721'4&Q7r4r2%33291&QO&QF&QA%211%43D61%C3:61p0<1pU@F1pU4J1pU2L1").
Proof.
intros i m r H. rewrite (refusal_b_errnos i m r (mkInjectedArm 222 FamAlloc mmap_errnos));
[| rewrite H; discriminate | rewrite H; exact injected_arm_222].
cbn [ia_errnos]. unfold mmap_errnos. apply ret_in_errnos_1.
Qed.
Lemma refusal_b_mprotect : ltac2:(TCodec.tc2 tcn__Scfg "M'QD'QB'RKyR0%211'='@&RL&QIr3%211%4281+W2%83721'4&Q7r4r2%33291&QO&QF&QA%211%43D61%C3:61p0<1pU@F1pU4J1pU2L1").
Proof.
intros i m r H. rewrite (refusal_b_errnos i m r (mkInjectedArm 226 FamAlloc mprotect_errnos));
[| rewrite H; discriminate | rewrite H; exact injected_arm_226].
cbn [ia_errnos]. unfold mprotect_errnos. apply ret_in_errnos_1.
Qed.
Lemma injected_family_off_alloc : ltac2:(TCodec.tc2 tcn__Scfg "Q7'I'QD'@'=&RLyR0&QIr2%211%5241r1%83921'?+VF%;3<71+VH%=3>91+VN%?3@;1+W2%A3B=1%9231%:261%;291'4&Q2r5r4%3221&8&Q9%115%311%N3951p0;1p0H1pU>Q21pU2Q41pTBQ61").
Proof.
intros cfg i n Hn Hcases. unfold injected_family_off. rewrite Hn.
destruct Hcases as [-> | [-> | [-> | ->]]];
[ rewrite injected_arm_214 | rewrite injected_arm_216
| rewrite injected_arm_222 | rewrite injected_arm_226 ]; reflexivity.
Qed.
Lemma injected_family_off_openat : ltac2:(TCodec.tc2 tcn__Scfg "I'I'QD'='@&RLyR0&QIr1%211%5241+QH%93821'4&Q2r3r2%3221&8&Q:%115%311%C3951p0;1pU2F1pTBH1").
Proof.
intros cfg i Hn. unfold injected_family_off. rewrite Hn, injected_arm_56. reflexivity.
Qed.
Lemma not_spurious_on : ltac2:(TCodec.tc2 tcn__Scfg "G'I'QD'QB'QC'='4&Q2r4r3%3221(6%73621&>&Q;r5r2%342981%511p071pTF@1pU4B1pU2D1pTBF1").
Proof. exact spurious_refusal_family_on. Qed.
Lemma not_spurious_nonrefusal : ltac2:(TCodec.tc2 tcn__Scfg "J'I'QD'QB'QC'='4&Q7r3r2&QEr1%211%63541(6%:3921&>&Q;r5r4%3421<;%511p071pTFC1pU4E1pU2G1pTBI1").
Proof. exact spurious_refusal_not_refusal. Qed.
Lemma not_spurious_forced : ltac2:(TCodec.tc2 tcn__Scfg "Q7'I'QD'QB'QC'7'QG%211&Q@r6r5(Ar3r2r1%44;321%83761'='4&Q7r7&QEr4%211%534?1(;%93821p0;1pTNE1pU6J1pTHJ1&>&Q;%14G;ED%311p051pTFQ01pU4Q21pU2Q41pTBQ61").
Proof.
intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.
Lemma spurious_intro : ltac2:(TCodec.tc2 tcn__Scfg "Q@'I'QD'QB'QC'7'QG%211'='4&Q2r7r6%3221(;%73621&Q7&QEr5%211%43981%=3<17&Q@r8(Ar4r3%34G921%635A1r9%=1B%?3281(6%I3H21&Q;r;r:%34218>p051p0;1p0C1p0J1pU0Q31pU8Q81pTJQ81pTFQ91pU4Q;1pU2Q=1pTBQ?1").
Proof.
intros cfg i m eff eff1 m1 evs1 Hoff Hr Hspec Hnr.
split; [exact Hoff|]. split; [exact Hr|]. exists eff1, m1, evs1. split; assumption.
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Definition fam_on (ms : machine_state) : Prop :=
forall x8, ms_svc_pending ms = Some x8 ->
injected_family_off scfg (sys_input segs ms x8) = false.
Lemma fam_on_instr : ltac2:(TCodec.tc2 tcn__Scfg "B'B'=':'RKyR0%211%411&Cr1%211(0%116%;3631&R0r2%211p041pU<A1").
Proof. intros ms H x8 Hx. rewrite H in Hx. discriminate Hx. Qed.
Lemma fam_on_none : ltac2:(TCodec.tc2 tcn__Scfg "N'B'RKyR0%211'=':%113&Cr2%211(2r1%2291%93741'F%:11&Q1&RL%12@:%311(0%117%B3731&R0r4%211p041p0>1pV2I1pU<M1").
Proof.
intros ms x8 Hsvc Harm y Hy. rewrite Hsvc in Hy. injection Hy as <-.
unfold injected_family_off. change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Harm. reflexivity.
Qed.
Lemma fam_on_sysno : ltac2:(TCodec.tc2 tcn__Scfg "Q2'B'RKyR0%211'@'=':%114&Cr3%211(2r2%22:1%93741&RL%12>7%<3=15'F%=11&Q1%11<(0%115%C3531&R0r6%211p041p0<1p0@1pU>K1pV2M1pU<Q11").
Proof. intros ms x8 n Hsvc <- Harm. exact (fam_on_none ms x8 Hsvc Harm). Qed.
Lemma fam_on_mayfail : ltac2:(TCodec.tc2 tcn__Scfg "Q7'B'RKyR0%211'F'=':%114&Cr3%211(2r2%22:1%93741%91;&Q1&RL%12@9%311%92@8%@3621'4&NvRH&Q0%11A%4231(;%H3721&R0r6%211p041p0=1p0E1pT4Q01pV2Q21pU<Q61").
Proof.
intros ms x8 a Hsvc Harm Hfam y Hy. rewrite Hsvc in Hy. injection Hy as <-.
unfold injected_family_off. change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Harm, Hfam. reflexivity.
Qed.
Lemma fam_on_openat : ltac2:(TCodec.tc2 tcn__Scfg "Q1'B'RKyR0%211'=':%113&Cr2%211(2r1%2291%93741'@&RL%12>8+QH%>3421'4&Q:vRH%211(;%D3521&R0r5%211p041p0;1p0A1pV2L1pU<Q01").
Proof.
intros ms x8 Hsvc Hno Hfs.
apply (fam_on_mayfail ms x8 (mkInjectedArm 56 FamFs openat_errnos) Hsvc);
[rewrite Hno; exact injected_arm_56 | exact Hfs].
Qed.
Lemma fam_on_exit : ltac2:(TCodec.tc2 tcn__Scfg "N'B'RKyR0%211'=':%113&Cr2%211(2r1%2291%93741'?'@&RL%12?9+RM%?3421+RN%A3641%8231&R0r4%211p041p0>1pV2I1pU<M1").
Proof.
intros ms x8 Hsvc [H|H]; eapply fam_on_sysno; eauto using injected_arm_93, injected_arm_94.
Qed.
Lemma sstep_cfg_of_sstep : ltac2:(TCodec.tc2 tcn__Scfg "M'B'QB'7'QG%211'Q?'Q<vRI(Q3r4r3%3221r2r1%847321&R0r5%211'Q=vRHr6%=215%45?31=<p061p0:1pUFD1pTDF1pU:J1pU<L1").
Proof.
intros ms model e st Hss Hon.
inversion Hss; subst;
[ eapply sstep_cfg_instr; eassumption
| eapply sstep_cfg_instr_fault; eassumption
| eapply sstep_cfg_instr_unmodeled; eassumption
| eapply sstep_cfg_syscall; try eassumption; apply not_spurious_on; apply Hon; assumption
| eapply sstep_cfg_syscall_materialization_fault; try eassumption;
apply not_spurious_on; apply Hon; assumption
| eapply sstep_cfg_exit; eassumption
| eapply sstep_cfg_killed; eassumption
| eapply sstep_cfg_syscall_unmodeled; eassumption ].
Qed.
Lemma sstep_cfg_of_sstep' : ltac2:(TCodec.tc2 tcn__Scfg "I'M'7'QG%211'Q?'Q<vRIr3r2r1%544321&R0&Lr4%211%411'Q=vRHr5%35=216<p051p0;1pUFB1pTDD1pT6H1").
Proof. intros [ms model] e st; cbn. apply sstep_cfg_of_sstep. Qed.
Lemma sstep_of_sstep_cfg : ltac2:(TCodec.tc2 tcn__Scfg "C'M'7'QG%211'Q?'Q=vRIvRHr3r2r1%6554321'Q<r4%248165p041pUF<1pTD>1pT6B1").
Proof. intros c e st H. exact (sstep_cfg_sub segs scfg c e st H). Qed.
Lemma star_cfg_one : ltac2:(TCodec.tc2 tcn__Scfg "D'M'7'QG%211'Q=vRIvRHr3r2(Hr1%211%8576541'Q>r4%25:9187p041pT8A1pTL?1pT6C1").
Proof.
intros c evs c' H. rewrite <- (app_nil_r evs).
eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.
Lemma star_cfg_trans : ltac2:(TCodec.tc2 tcn__Scfg "I'M'7'QG%211'Q>vRIvRHr5r4r3%6554321r2%8576431r7&3r6%23>18%=5<;418p061p091pT@D1pV0B1pT>F1pUND1pT<H1").
Proof.
intros c1 tr1 c2 tr2 c3 H12 H23.
induction H12 as [c | c evs c' tr c'' Hs Hst IH].
- exact H23.
- rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H23].
Qed.
Lemma obs_trace_cfg_nil : ltac2:(TCodec.tc2 tcn__Scfg ":'M&Q5vRIvRHr1(9'QG%211%746541pT:91").
Proof.
intros c0. exists [], c0. split; [apply star_cfg_refl | exact I].
Qed.
Lemma sstep_cfg_halted_none : ltac2:(TCodec.tc2 tcn__Scfg "N'M'7'QG%211'Q?'Q=vRIvRHr3r2r1%6554321'=':'RKyR0%211%411&QJ&Kr4%211%411(0%118%=3831p0?1pUFG1pTDI1pT6M1").
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.
Lemma star_cfg_halted_nil : ltac2:(TCodec.tc2 tcn__Scfg "Q6'M'7'QG%211&>'=':'RKyR0%211%411&QJ&Kr3%211%411(0%118%=3831%?11'Q>vRIvRHr4r2%55432<1'<(9%11J%H3J61r5%J3OB1%6231p081p0?1pT8Q31pULQ11pT6Q51").
Proof.
intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
- split; reflexivity.
- exfalso. apply Hh. eapply sstep_cfg_halted_none. exact Hss.
Qed.
Lemma reaches_error_cfg_here : ltac2:(TCodec.tc2 tcn__Scfg "A'M'7'QG%211'Q=vRIvRHr2r1(G%6554321&Q6r3%23871p041pTL<1pT6@1").
Proof.
intros c evs H. exists [], c, evs. split; [apply star_cfg_refl | exact H].
Qed.
Lemma reaches_error_cfg_step : ltac2:(TCodec.tc2 tcn__Scfg "F'M'7'QG%211'Q=vRIvRHr3r2(Hr1%211%8576541&Q6%13986r5%33;:1p031p061pT8C1pTLA1pT6E1").
Proof.
intros c evs c' Hs (tr & c2 & evs2 & Hst & He).
exists (evs ++ tr), c2, evs2. split; [eapply star_cfg_step; eassumption | exact He].
Qed.
End WithSegs.
