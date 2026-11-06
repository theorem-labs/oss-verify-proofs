(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatSim MmapSim ShapeAlg DivergeSim LazyFrame SymTac SpinAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__NoReserveK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Init.Specif."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.BvBase."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.Specs."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall."; "LinuxProcessSemantics.Riscv.DecodeC."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.DivergeSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.LazyFrame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.NoReserveK.WithFP1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.NoReserveK.WithFP1.WithSegs."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1O"; "1Some"; "1app"; "1bool"; "1cons"; "1false"; "1length"; "1list"; "1nat"; "1nil"; "1option"; "1pair"; "1prod"; "1true"; "1unit"]; ["2I"; "2and"; "2eq"; "2ex"; "2not"; "2or"; "3le"; "4proj1_sig"; "5firstn"; "5map"; "6Z"; "7len_word"; "8errno_ret_in"; "9Fs"; ":Segment"; ";Ok"]; [";Unmodeled"; "<Build_machine_state"; "<MachineOk"; "<access_report"; "<fetch_word"; "<is_ecall"; "<machine_result"; "<machine_state"; "<memory_access"; "<mkAccessReport"; "<ms_gpr"; "<ms_read_bytes"; "<ms_svc_pending"; "<set_gpr0"; "<step_accesses"; "=SNext"]; ["=advance_past_svc"; "=apply_effect"; "=config"; "=mkCfg"; "=sstep"; "=step_to"; "=sys_input"; ">syscall_spec"; "?MemCopy"; "?Model"; "?SyscallEffect"; "?WriteEv"; "?alloc_top"; "?errno_ret"; "?event"; "?lazy_interior"]; ["?m_fs"; "?m_halted"; "?m_vm_lazy"; "?m_vmmaps"; "?materialize_model_accesses"; "?mkEffectU"; "?page_round_up_Z"; "?page_size"; "?region_free"; "?syscall_effect_accesses"; "?vm_maps"; "?vm_reserved"; "?with_copyins"; "@mmap_anon_b"; "@mmap_errnos"; "@mmap_modeled_b"]; ["@mmap_noreserve_b"; "@mmap_off_aligned_b"; "Aw_is0"; "Bdecode_any"; "CBranch"; "CJal"; "Cbranch_cond"; "Cinstr"; "Dbvmap"; "Ebranch_taken"; "Fbuf_modeled"; "Ffd1chan"; "Gto_spin"; "Haccess_outside_range"; "Haccesses_outside_lazy"; "Imunmap_args_ok"]; ["Imunmap_eff"; "Imunmap_model"; "Ipage_round_up"; "Kmsteps_acc"; "Jgrant_ok_nr"; "Jmmap_args_ok_noreserve"; "Jmmap_model_noreserve"; "Lbtgt"; "Lfp_csr"; "Lfp_regs"; "Lgetr"; "Lmkst"; "Lv_addi"; "MTSet"; "Mnode_ok"; "Mrealizes"]; ["Mt_write_ch"; "Mwr_index"; "Nsrealizes"; "OIn"; "Padd"; "Ple"; "Plt"; "Pmodulo"; "0T"; "0a"; "0accs"; "0accs'"; "0accs1"; "0accs2"; "0buf"; "0c"]; ["0c'"; "0e"; "0eff"; "0evs"; "0fx"; "0hint"; "0i"; "0imm"; "0lazy"; "0len"; "0lo"; "0m"; "0mem"; "0model"; "0model'"; "0ms"]; ["0ms'"; "0ms''"; "0n"; "0n'"; "0pc"; "0r"; "0ranges"; "0regs"; "0rom"; "0rs1"; "0rs2"; "0scfg"; "0segs"; "0st"; "QBV"; "QZ_to_bv"]; ["Qbv"; "Qbv_signed"; "Qbv_unsigned"; "0sz"; "0us"; "0w"; "0x"; "0x8"; "0zs"]]).
Section WithFP1.
Context {fx : FPState}.
Lemma materialize_syscall_effect_nil : ltac2:(TCodec.tc2 tcn__NoReserveK "Q7'QI'U0yR0%211'8'=%1233%311'B';%11:&R4r4&R9(R5r3(:y8%A11%?11%?2A1%511r2r1'QH%911'9%F2H1%<11%?6>87641%A11%D2C1(2%12Q1E%J3H31pZ:L1pZBM1pY<Q21pXHQ61").
Proof. intros m r zs us. exact (materialize_model_accesses_nil m). Qed.
Lemma materialize_syscall_effect_copyin_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "QE'QI'U0yR0%211'9&RN(5'=%1254(<r2r1%349821(:%116%93731&R2r4%211%>241'B';%11F&R4r5&R9&R<r3%C4IH1B%G3E1?(R5'8y8%Q011%311%L2Q01%G11%N2Q2Q2%I11'QH%K11%;6H5331K%@2=1%B11%E2D1(2%12Q>F%K3I31p0M1pY6Q=1pWDQ?1pY<Q@1pXHQD1").
Proof.
intros m r a n Hout.
exact (materialize_model_accesses_disjoint m [(a, n)] Hout).
Qed.
Lemma materialize_munmap_eff_nil : ltac2:(TCodec.tc2 tcn__NoReserveK "B'QI'Q7'B';%114&R4r2&R9&S0r1%211%411%7261(2%12>8%=3;31pY0?1pXHA1").
Proof. intros m ms. exact (materialize_model_accesses_nil m). Qed.
Lemma access_outside_range_mono : ltac2:(TCodec.tc2 tcn__NoReserveK "F'U0yR0%211'9'Fr3r4%3221&RMr6r5r2%443271r7%641489p031p091pZ8?1pXF@1pY8@1pY6A1pWDC1").
Proof.
intros a n n' lo sz Hle [Hnw Hd].
split; [lia | destruct Hd as [Hd | Hd]; [left; lia | right; exact Hd]].
Qed.
Lemma accesses_outside_lazy_incl : ltac2:(TCodec.tc2 tcn__NoReserveK "L'8'='U0yR0%211'9%5221%711%7244%911&SCr1r3%33721r2r5%63:21p041pZ><1&RNr4%2217%322:p021p061pXB@1pWHC1pWFD1").
Proof.
intros accs accs' lazy Hincl Hout a n lo sz Hin Hlz.
exact (Hout a n lo sz (Hincl _ Hin) Hlz).
Qed.
Lemma accesses_outside_lazy_app_l : ltac2:(TCodec.tc2 tcn__NoReserveK "G'8'='U0yR0%211'9%5221%711%7244%911&RN&3r3r2%33821r1%6221r4%8215p031pXB;1pWL>1pWJ?1").
Proof.
intros accs1 accs2 lazy Hout.
apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
intros x Hx. apply in_or_app. left. exact Hx.
Qed.
Lemma accesses_outside_lazy_app_r : ltac2:(TCodec.tc2 tcn__NoReserveK "F'8'='U0yR0%211'9%5221%711%7244%911&RN&3r3r2%33821r1%6221%7254p021pXB:1pWL=1pWJ>1").
Proof.
intros accs1 accs2 lazy Hout.
apply (accesses_outside_lazy_incl (accs1 ++ accs2)); [| exact Hout].
intros x Hx. apply in_or_app. right. exact Hx.
Qed.
Lemma accesses_outside_lazy_shrink : ltac2:(TCodec.tc2 tcn__NoReserveK "Q1'U0yR0%211'9'8'=%1244%311'Fr2r3%3221&RN(5%92<;(<r5r4%34@?21(:%116%83731%:21=r6%94FE17%<3;15%>21@p051p0A1pXBF1pY6K1pXDL1pWDN1").
Proof.
intros a len n lazy Hle Hout a' n' lo sz Hin Hlz.
destruct Hin as [Hin | []]. injection Hin as Ha Hn. subst a' n'.
apply (access_outside_range_mono a len n lo sz Hle).
apply (Hout a len lo sz); [left; reflexivity | exact Hlz].
Qed.
Definition mmap_model_noreserve (a n : word) (m : Model) : Model :=
vm_add_lazy a n (mmap_model a n m).
Lemma mmap_model_noreserve_halted : ltac2:(TCodec.tc2 tcn__NoReserveK "C'U0yR0%211'QI'B';%114&R1&S6r3r2r1%43321%611%713%;3921pXH=1pY6?1pWD@1").
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fs : ltac2:(TCodec.tc2 tcn__NoReserveK "B'U0yR0%211'QI'B&M&R0&S6r3r2r1%43321%611%713%:3921pXH<1pY6>1pWD?1").
Proof. reflexivity. Qed.
Lemma mmap_model_noreserve_fd1chan : ltac2:(TCodec.tc2 tcn__NoReserveK "A'U0yR0%211'QI&RKr1%211&S6r4r3r2%43321%811p071pXH;1pY6=1pWD>1").
Proof. intros a n m H. exact H. Qed.
Lemma mmap_model_noreserve_lazy : ltac2:(TCodec.tc2 tcn__NoReserveK "I'U0yR0%211'QI'B'8'=%1255%311&R2&S6r3r2r1%43321%611&3&QO%1276%:16%43=21%A3=61pXHC1pY6E1pWDF1").
Proof. reflexivity. Qed.
Definition mmap_args_ok_noreserve (ms : machine_state) : Prop :=
ms_gpr ms 1 <> Z_to_bv 64 0 /\ ms_gpr ms 2 = Z_to_bv 64 3
/\ ms_gpr ms 3 = Z_to_bv 64 16418 /\ ms_gpr ms 4 = Z_to_bv 64 (-1)
/\ ms_gpr ms 5 = Z_to_bv 64 0.
Lemma mmap_args_ok_noreserve_gates : ltac2:(TCodec.tc2 tcn__NoReserveK "Q4'Q7&S5r1%211'A'B'4&RA&Q:r2u5%3221%511(>%93821&R=u3%9281%311%>3=16&RBu1%>2=1%311(6%D3C21&R?u2%D2C1%331<B%I3H1A%K261%L2=1%M2C1p0O1pY0Q31").
Proof.
intros ms (H1 & H2 & H3 & H4 & H5).
split; [unfold mmap_off_aligned_b; rewrite H5; reflexivity|].
split; [unfold mmap_anon_b; rewrite H3; reflexivity|].
split; [unfold w_is0; apply bv_eqb_neq; exact H1|].
unfold mmap_modeled_b. rewrite H2, H3, H5. reflexivity.
Qed.
Lemma mmap_noreserve_b_flags : ltac2:(TCodec.tc2 tcn__NoReserveK ":'B'4&R@&TOyR0+`Q2%3221%511(>%93821").
Proof. reflexivity. Qed.
Definition grant_ok_nr (hint : word) (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Lemma grant_ok_nr_unpack : ltac2:(TCodec.tc2 tcn__NoReserveK "QF'U0yR0%211'QI'J'B'4&S4r4r3r2r1%544321(>%93821'A&SG&U2%12A9&R7%4221z%A3B21&SF%1236&SE&SD%129A&QL&R3%11F%311%7251&R8&3'=%12Q2Q2&R;%118&R:%11:%73531&TO%12Q:Q1%;33Q31%Q83Q71Q0%O2>1%Q02G1%Q12J1p0Q31pY6Q>1pWDQA1pXHQA1pX<QC1").
Proof.
intros hint m a n H. unfold grant_ok_nr in H.
rewrite !andb_true_iff in H.
destruct H as [[[H1 H2] H3] H4].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
auto 6.
Qed.
Lemma grant_nr_not_errno : ltac2:(TCodec.tc2 tcn__NoReserveK "N'U0yR0%211'QI'J&SEzr1%3221'B'4&S4r5r4r3r2%544321(>%93821&L&R>%2218(6%>3=21p061p0A1pY6F1pWDI1pXLI1pX<K1").
Proof.
intros hint model a n Hn Hg.
destruct (grant_ok_nr_unpack _ _ _ _ Hg) as (_ & _ & Hce & _).
apply errno_ret_in_below; [reflexivity|].
alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Lemma mmap_fail_ok_noreserve : ltac2:(TCodec.tc2 tcn__NoReserveK "QL'8'N%211'Q7'U0yR0%211'QI'J'B&U2r3%2271+VN%53621&S5r5%211&SC&R>%23<91&QG&QFr8r7r6%43321(O'QJ(R5&QMr4%211(:'=y8%Q011%Q511%42Q01%611%62Q2Q2%811'QH%:11'9%;2Q71%=11%B6?86641'QN%@11%G4F3Q21%N3IQ31p0Q01p0Q41p0Q81pX4Q?1pXLQA1pZ@QC1pY0QG1pYJQI1").
Proof.
intros segs ms x8 model e Hno Ha HIn.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite errno_ret_in_intro by assumption. reflexivity.
Qed.
Lemma mmap_succ_ok_noreserve : ltac2:(TCodec.tc2 tcn__NoReserveK "R='8'N%211'Q7'U0yR0%211'QI'B'J&U2r3%2271+VN%63521&S5r5%211'4&S4&Q:r6(1%3221r4&R6u1%7261%B2G1%411%;476C1(>%H3>21&QG&QFr8r7%3321@(O'QJ(R5(:'=y8%Q811%Q=11%42Q81%611(5%72Q;Q;(<&S2%Q02@J%211%44Q@Q@N1%>16%83721'QH%A11'9%B2QF1%D11%F6Q6?6741&S6%13Q8;Q@'QN%I11%M4L531%Q33OQD1p0Q51p0QE1p0QI1pWDR21pXLR21pZ@R41pY0R81pYJR:1").
Proof.
intros segs ms x8 model a Hno Ha Hg.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj2 (syscall_spec_mmap _ _ _ _ _ Hno)). apply check_mmap_sound_ok.
unfold check_mmap. cbv beta.
rewrite Hoff, Hanon, Hl, Hmb. cbn [negb]. cbv beta iota zeta.
rewrite (grant_nr_not_errno (ms_gpr ms 0) model a
(page_round_up_Z (bv_unsigned (ms_gpr ms 1))));
[ | apply page_round_up_Z_nonneg; pose proof (u64_range (ms_gpr ms 1)); lia
| exact Hg ].
unfold grant_ok_nr in Hg. rewrite !andb_true_iff in Hg.
destruct Hg as [[[H1 H2] H3] H4].
rewrite Hflags.
unfold mmap_noreserve_backed_ok, with_mmap_backing.
rewrite mmap_noreserve_b_flags.
rewrite H1, H2, H3, H4. cbn [andb].
unfold page_round_up. cbn [listNN_eqb]. rewrite !bv_eqb_refl.
reflexivity.
Qed.
Lemma mmap_ok_inv_noreserve : ltac2:(TCodec.tc2 tcn__NoReserveK "S:'8'N%211'Q7'U0yR0%211'QI'QJ'QN%:11'B'J&U2r5%22:1+VN%63521&S5r7%211&QG&QFr9r8%33216r6(Or4r3%34F@21%:3651'A(:%11I%H3I71'E'C&SCr1&R>%33M21(R5&QM%115'=y8%Q;11%Q@11%42Q;1%A11%62Q=Q=%C11'QH%E11'9%;2QB1%H11%@6>86641%Q@3QCQ81%QA3QEQ2Q4%M221%N2E1qX4QC1%K2QD1'4&S4&Q:r:(1%3221&R6u1%6251%QM2R51%411%:46QDQ51(>%R33=21(5(<&S2%119%34R=R=Q<1%53Q11Q0%Q;6Q>Q31Q1OL%R;3R>R31&S6%13QA6R0%R>3RBQO1%QJ241%QK2=1qWDRF1%QH2RG1%QJ2N1%QO2QL1p0R11p0R=1p0RA1pX8RI1pXNRM1pX6RM1pXLRO1pZ@S11pY0S51pYJS71").
Proof.
intros segs ms x8 model eff model' evs Hno Ha Hspec.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
destruct Ha as (_ & _ & Hflags & _ & _).
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply check_mmap_complete_ok in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
rewrite Hflags in Hspec.
unfold mmap_noreserve_backed_ok, with_mmap_backing in Hspec.
rewrite mmap_noreserve_b_flags in Hspec.
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
- rewrite andb_true_r in Hspec.
destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) <=? alloc_top (m_vmmaps model))%Z
&& region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) r
(Z_to_bv 64 (page_round_up_Z (bv_unsigned (ms_gpr ms 1))))) eqn:Hcond;
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
+ unfold grant_ok_nr. exact Hcond.
+ unfold page_round_up. reflexivity.
+ reflexivity.
Qed.
Lemma mmap_no_unmodeled_noreserve : ltac2:(TCodec.tc2 tcn__NoReserveK "Q4'8'N%211'Q7'U0yR0%211'QI'B'J&U2r2%2271+VN%63521&S5r4%211&D&QG&QFr6r5%33217r3(Q0'QJ%211%93541%;11p0=1p0A1pXLI1pZ@K1pY0O1pYJQ11").
Proof.
intros segs ms x8 model Hno Ha Hspec.
destruct (mmap_args_ok_noreserve_gates ms Ha) as [Hoff [Hanon [Hl Hmb]]].
apply (proj1 (syscall_spec_mmap _ _ _ _ _ Hno)) in Hspec.
apply (check_mmap_complete_unmodeled _ _ _ _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hspec.
unfold check_mmap in Hspec. cbv beta in Hspec.
rewrite Hoff, Hanon, Hl, Hmb in Hspec. cbn [negb] in Hspec.
cbv beta iota zeta in Hspec.
assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
rewrite E in Hspec. cbv beta iota in Hspec.
match type of Hspec with (if ?b then _ else _) = _ => destruct b end;
discriminate.
Qed.
Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma sstep_munmap_inv_lazy : ltac2:(TCodec.tc2 tcn__NoReserveK "R;'Q7'QI'U0yR0%211'8'QN%211'QE'B';%117&R1r4%211(0%11<%83631&Q<r6%211(2%12B9%>3<31'J&U2r5%22H1+VG%D3521&ROr8r7%3221'QDvTL(QCr9%2217%5441D='A(:%11Q4%Q23Q4;1(Q?&Q@&QAr:&S0%112%4231%611&S1&Q:(1%2281&S2u1%52;1%311%8351G%I2:1%B11%QF3QGQ<1%H2E1p0J1p0Q11p0Q61p0Q=1p0QD1pYLQN1pX8R01pZ@R41pXLR81pY0R:1").
Proof.
intros ms model x8 evs st Hh Hsvc Hno Hargs Hss.
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
rewrite materialize_munmap_eff_nil in Hmat;
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
rewrite materialize_munmap_eff_nil in Hmat;
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
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (munmap_ok_inv segs ms x8 model eff model' evs0 Hno Hargs H3) as (_ & Hm & _);
subst model'; rewrite m_killed_of_m_halted_none in H6;
[ discriminate | rewrite munmap_model_halted; exact Hh ]
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
Lemma node_munmap_lazy : ltac2:(TCodec.tc2 tcn__NoReserveK "R3'Q7'QI'U0yR0%211'B';%113&R1r2%211(0%118%83631&Q<r4%211(2%12>9%>3<31'J&U2r3%22D1+VG%D3521&ROr6r5%3221&S>vTLvTK(QCr7%2218'?(:'QN%211q041&Q@&QAr8&S0%112%4231%611&S1&Q:(1%2281&S2u1%52;1%311%8351F%H2:1q0F1%M6LKHGC1p0O1p0Q41p0Q;1p0QB1pZ@QL1pXLR01pY0R21").
Proof.
intros ms model x8 Hh Hsvc Hno Hargs.
apply (node_ok_of_pnode_sysno segs scfg ms model x8 215%Z); [exact Hsvc | exact Hno | exact injected_arm_215 |].
split.
- intros []. apply (sstep_syscall segs ms model x8 (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
+ exact Hh.
+ exact Hsvc.
+ apply munmap_ok; assumption.
+ rewrite munmap_model_halted; exact Hh.
+ apply materialize_munmap_eff_nil.
- intros e st Hss.
destruct (sstep_munmap_inv_lazy ms model x8 e st Hh Hsvc Hno Hargs Hss)
as [-> ->].
exists tt. split; reflexivity.
Qed.
Lemma srz_munmap_lazy : ltac2:(TCodec.tc2 tcn__NoReserveK "R1'Q7'QI'U0yR0%211&S='B';%114&R1r3%211(0%119%83631&Q<r5%211(2%12?9%>3<31'J&U2r4%22E1+VG%D3521&ROr7r6%3221'SBvTLvTK(QC&Q@&QAr8&S0%112%4231%611&S1&Q:(1%2281&S2u1%52;1%311%8351F%A2:1%E4DC1Q4r9%D21A%H4GF1Jp041p0K1p0Q01p0Q71p0Q>1pWBQH1pZ@QJ1pXLQN1pY0R01").
Proof.
intros ms model x8 T Hh Hsvc Hno Hargs Hc.
eapply srz_silent1; [apply (node_munmap_lazy ms model x8); assumption | exact Hc].
Qed.
Lemma sstep_write_next_inv_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "T0'Q7'QI'U0yR0%211'8y8%511%311'QN%511'QB'B';%11:&R1r5%211(0%11?%83631&RN(5'='9%22E1(<&Q:r7u1%3221&7r4%22J1%84N:41(:%11;%?3<31&R2r6%211%D241&RK%11?&Q<r9%211(2%12Q<D%Q53Q331'J&U2r8%22QB1+R0%Q;3521r;(1%O221&TO+1%22QJ1%QB3QJ41%QB1QG&Q;r<%Q721Q5u2%Q9231%53431%G2QNI%QK3821'Fr:%Q;2R31%32Q>1'QDvTL(QCr>r=%3221(Q?%11Q6%8473;1'C'Ar1%@2QK1%QJ2RB9%B231&I(QK%11Q0&H%13RH8?%54RIRG31%RE3RGQ01&Q@&Q=r@&K%12RO7%4231%611r?%L221%RO3S0QC1%F2;1%G2C1%H2F1qY6RG1%K2RH1p0M1p0Q71p0Q<1p0QF1p0QN1p0R51p0R<1p0R?1p0S51pX2S?1pX8SA1pWNSD1pZ@SI1pXLSM1pY0SO1").
Proof.
intros ms model x8 buf evs c' Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss.
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
rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
(accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
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
H6 : m_killed ?model' = Some _ |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hnb H3)
as (n & _ & _ & _ & Hm & _);
subst model'; rewrite (m_killed_of_m_halted_none _ Hh) in H6; discriminate
end.
Qed.
Lemma sstep_write_inv_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "T4'Q7'QI'U0yR0%211'8y8%511%311'QN%511'QE'B';%11:&R1r5%211(0%11?%83631&RN(5'='9%22E1(<&Q:r7u1%3221&7r4%22J1%84N:41(:%11;%?3<31&R2r6%211%D241&RK%11?&Q<r9%211(2%12Q<D%Q53Q331'J&U2r8%22QB1+R0%Q;3521r;(1%O221&TO+1%22QJ1%QB3QJ41%QB1QG&Q;r<%Q721Q5u2%Q9231%53431%G2QNI%QK3821&RJr:%211'F%Q=2R5D%22Q@1'QDvTL(QCr?r>%3221%6451L;'C'Ar1%=2QK1%QJ2RB7%?231r=&I(QK%11Q1&H%13RI9>%54RJRH31%RF3RH71(Q?&Q@&Q=rA&K%12S18%4231%611r@%L221%:11%S23S3Q=1%I2=1%J2F1%K2I1qY6RJ1%N2RK1p0Q01p0Q81p0Q<1p0Q@1p0QJ1p0R21p0R91p0R@1p0RC1p0S91pYLSC1pX8SE1pWNSH1pZ@SM1pXLT11pY0T31").
Proof.
intros ms model x8 buf evs st Hh Hout Hfd Hsvc Hno Hg Hr Hcnt Hnb Hss.
destruct st as [c'|].
- destruct (sstep_write_next_inv_disjoint ms model x8 buf evs c'
Hh Hout Hfd Hsvc Hno Hg Hr Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
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
as (n & _ & Hn2 & Heff & Hm & _);
subst eff model';
rewrite (materialize_syscall_effect_copyin_disjoint model _ _ n
(accesses_outside_lazy_shrink _ _ n _ Hn2 Hout)) in Hmat;
discriminate
end.
+ match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
end.
Qed.
Lemma node_write1_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "SM'Q7'QI'U0yR0%211'8y8%511%311'B';%117&R1r3%211(0%11<%83631&RN(5'='9%22B1(<&Q:r5u1%3221&7r2%22G1%84K:41(:%11;%?3<31&R2r4%211%D241&RK%11?&Q<r7%211(2%12Q9D%Q53Q331'J&U2r6%22Q?1+R0%Q;3521r9(1%O221&TO+1%22QG1%QB3QG41%QB1QD&Q;r:%Q721Q5u2%Q9231%53431%G2QKI%QK3821&RJr8%211'F%Q=2R2D%22Q@1&S>vTLvTK(QCr=r<%3221&SA%11E&I'QN(QK%11M&H&G'Ar1%D2R21%R12RF=%F231%5231qY6R;1%83R<16r;%;3RL21%@4RM?=1qX>B1&Q@&Q=r>&K%12S37%4231%611%O21NqX>K1%Q46Q3Q2NL:1p0Q61p0Q:1p0Q>1p0QH1p0R01p0R71p0R>1p0RA1p0S71pWNSA1pZ@SF1pXLSJ1pY0SL1").
Proof.
intros ms model x8 buf Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb.
apply (node_ok_of_pnode_sysno segs scfg ms model x8 64%Z); [exact Hsvc | exact Hno | exact injected_arm_64 |].
split.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig].
rewrite <- (apply_effect_copyins_no_write ms (len_word (firstn n buf))
[(ms_gpr ms 1, n)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, n)]
(mkEffect (len_word (firstn n buf)) [] [])) model
model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
+ exact Hh.
+ exact Hsvc.
+ apply write1_ok_n; assumption.
+ exact Hh.
+ apply materialize_syscall_effect_copyin_disjoint.
exact (accesses_outside_lazy_shrink _ _ n _ Hn2 Hout).
- intros e st Hss.
destruct (sstep_write_inv_disjoint ms model x8 buf e st
Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hss)
as (n & Hn1 & Hn2 & -> & ->).
exists (exist _ n (conj Hn1 Hn2)). split; reflexivity.
Qed.
Lemma srz_write1_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "SK'Q7'QI'U0yR0%211'8y8%511%311&S='B';%118&R1r4%211(0%11=%83631&RN(5'='9%22C1(<&Q:r6u1%3221&7r3%22H1%84L:41(:%11;%?3<31&R2r5%211%D241&RK%11?&Q<r8%211(2%12Q:D%Q53Q331'J&U2r7%22Q@1+R0%Q;3521r:(1%O221&TO+1%22QH1%QB3QH41%QB1QE&Q;r;%Q721Q5u2%Q9231%53431%G2QLI%QK3821&RJr9%211'F%Q=2R3D%22Q@1r1%42QB1r2r=%QC2R91%8231'SBvTLvTK(QC&Q@&Q=rA&K&Hr>%23REQN1%42RF1%7261%911r@%<221%@4?>1Cp0B1p0G1pY6R?1r?%B21<&S@r<%23Q?1Q;%I4HG41p071p0Q21p0Q61p0Q:1p0QD1p0QL1p0R31p0R:1p0R=1p0S31pWBS=1pWNS?1pZ@SD1pXLSH1pY0SJ1").
Proof.
intros ms model x8 buf T Hh Hout Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
unfold t_write_ch.
apply (srz_node segs scfg (mkCfg ms model) (wr_index buf)
(fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
(fun i => mkCfg (advance_past_svc
(set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
model)
(fun _ => T) (wr_full buf Hnb)).
- apply (node_write1_disjoint ms model x8 buf); assumption.
- intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.
Inductive msteps_acc
: machine_state -> machine_state -> list (word * nat) -> Prop :=
| msta_refl : forall ms, msteps_acc ms ms []
| msta_step : forall ms ms1 ms2 ranges accs,
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms
= MachineOk (@mkAccessReport machine_state ms1 ranges) ->
msteps_acc ms1 ms2 accs ->
msteps_acc ms ms2 (ranges ++ accs).
Lemma msteps_acc_one : ltac2:(TCodec.tc2 tcn__NoReserveK "Q6'Q7'8&Q8%211'B';'U0yR0%211%411&Q<r3%211(0%116%;3631'Q6'Q3%11B%311&Q>vTLr4%3221(Q2(Q9r2%23K@1%42:1%I3:61'S3r5%231:Ep041p0C1pY>Q01pY2Q41pY0Q51").
Proof.
intros ms ms' ranges Hsvc Hstep.
rewrite <- (app_nil_r ranges).
eapply msta_step; [exact Hsvc | exact Hstep | apply msta_refl].
Qed.
Lemma msteps_acc_trans : ltac2:(TCodec.tc2 tcn__NoReserveK "J'Q7'8'='U0yR0%211'9%5221%711'S3r5r4r2%43321r7&3r3%23:61%93481p061p071pWL=1pWJ>1pY4G1pY2H1pY0I1").
Proof.
intros ms ms' ms'' accs1 accs2 H; revert accs2 ms''.
induction H as [ms | ms ms1 ms2 ranges accs Hsvc Hstep H IH];
intros accs2 ms'' H2; [exact H2|].
rewrite <- app_assoc. eapply msta_step; eauto.
Qed.
Lemma srz_msteps_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "Q@'Q7'QI'8'='U0yR0%211'9%5221%711&S='B';%117&R1r3%211(0%11<%83631'S3r6r5%33218&RNr4&R2%115%4231'SBvTLvTK(QCr7%221=%64541:r9%5214%94871@p041p0<1p0B1p0G1pWBQ11pWFQ31pXLQ<1pY2Q>1pY0Q?1").
Proof.
intros ms ms' model accs T Hh Hms; revert T;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros T Hout Hc; [exact Hc|].
eapply srz_step_disjoint;
[ exact Hh | exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.
Lemma rz_msteps_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "Q@'Q7'QI'8'='U0yR0%211'9%5221%711&S='B';%117&R1r3%211(0%11<%83631'S3r6r5%33218&RNr4&R2%115%4231'S?vTLvTK(QCr7%221=%64541:r9%5214%94871@p041p0<1p0B1p0G1pWBQ11pWFQ31pXLQ<1pY2Q>1pY0Q?1").
Proof.
intros ms ms' model accs T Hh Hms; revert T;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros T Hout Hc; [exact Hc|].
eapply rz_step_disjoint;
[ exact Hh | exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hc] ].
Qed.
Lemma ts_msteps_disjoint : ltac2:(TCodec.tc2 tcn__NoReserveK "Q1'Q7'QI'8'='U0yR0%211'9%5221%711'S3r4r3r1%43321&RNr2&R2%116%4231'RLvTLr5%3321<r7%53413p031p081p0>1pWFD1pXLM1pY2O1pY0Q01").
Proof.
intros ms ms' model accs Hms;
induction Hms as [ms | ms ms1 ms2 ranges accs Hsvc Hstep Hms IH];
intros Hout Hspin; [exact Hspin|].
eapply ts_step_disjoint;
[ exact Hsvc | exact Hstep
| exact (accesses_outside_lazy_app_l ranges accs _ Hout)
| apply IH; [exact (accesses_outside_lazy_app_r ranges accs _ Hout) | exact Hspin] ].
Qed.
End WithSegs.
End WithFP1.
Ltac stepacc_pipeline Hfetch Hecall Hdecode :=
unfold RiscvSemantics.step_accesses;
cbn [ms_pc ms_pc_val mkst];
rewrite Hfetch;
cbv beta iota;
unfold RiscvSemantics.decode_exec_accesses;
rewrite Hecall;
cbv beta iota;
rewrite Hdecode;
cbv beta iota zeta delta
[RiscvSemantics.interp_eff_accesses
RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.rget Sem.rset Sem.with_regs Sem.with_pc Sem.with_resv
Sem.inval_resv Sem.w0 Sem.w1
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom mkst];
rewrite ?bv_eqb0_is_x0.
Section WithFP2.
Context {fx : FPState}.
Lemma stepacc_opimm_gen : forall segs regs pc mem rom w op rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm op rd rs imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (sext 64 imm)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_shiftimm_gen : forall segs regs pc mem rom w op rd rs (sh : bv 6),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm op rd rs sh, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs) (zext 64 sh)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_op_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (alu64 op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_opimm32_gen : forall segs regs pc mem rom w rd rs (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 ALU_ADD (low32 (getr regs rs)) (sext 32 imm))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd rs imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_shiftimm32_gen : forall segs regs pc mem rom w op rd rs (sh : bv 5),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (ShiftImm32 op rd rs sh, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs)) (zext 32 sh))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs sh Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_op32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (alu32 op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_mul_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (mul_div op (getr regs rs1) (getr regs rs2)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_mul32_gen : forall segs regs pc mem rom w op rd rs1 rs2,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul32 op rd rs1 rs2, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (sext 64 (mul_div op (low32 (getr regs rs1)) (low32 (getr regs rs2)))))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rs2); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4; reflexivity.
Qed.
Lemma stepacc_branch_tk_gen : ltac2:(TCodec.tc2 tcn__NoReserveK "S5'8'N%211&RHy5'U0yR0%211%5241';y8%611%311p061yQ0%:11'RF%<1=y=%>11'B%<16&Q4r:r8%3221(2r5%22=1%93841'4&Q5r6%211(6%?3521'='RG'J%3221%O11&RCr7%211(<(RDr4r3%34@E21+4%64=<21%I2<1%Q03<91&RI&S:r<%221H%322N%53@21(>%Q83N21'Q6'Q3'Q7%211%411&Q>r>&S;vT4r=r;%4532A1QA%7261(Q2(Q9&S7&U1%12QLQC%32H1%<5;:19QI(:&Q8%211%93E41%;2E1%R23E=1p0K1p0Q41p0QF1p0QM1pX@R81pYFR;1pYDR<1pX0R>1pZ<R@1pYBRC1pXJRD1pY:RK1pY@RK1pYJS21").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_addsext; reflexivity.
Qed.
Lemma stepacc_branch_ft_gen : ltac2:(TCodec.tc2 tcn__NoReserveK "S2'8'N%211&RHy5'U0yR0%211%5241';y8%611%311p061yQ0%:11'RF%<1=y=%>11'B%<16&Q4r:r8%3221(2r5%22=1%93841'4&Q5r6%211(6%?3521'='RG'J%3221%O11&RCr7%211(<(RDr4r3%34@E21+4%64=<21%I2<1%Q03<91&RI&S:r<%221H%322N%53@21%Q73M1I'Q6'Q3'Q7%211%411&Q>r>&S;vT4r=r;%4532@1Q@%7261(Q2(Q9&S<%12EK%:59817QF(:&Q8%211%73C41%92C1%QO3C;1p0I1p0Q11p0QC1p0QJ1pX@R51pYFR81pYDR91pX0R;1pZ<R=1pYBR@1pXJRA1pY:RH1pY@RH1pYJRO1").
Proof.
intros segs regs pc mem rom w c rs1 rs2 imm Hfetch Hecall Hdecode Hc.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr in Hc; rewrite ?bv_eqb0_is_x0 in Hc.
destruct (is_x0 rs1); destruct (is_x0 rs2);
cbv beta iota; rewrite Hc; cbv beta iota;
rewrite b_npc4; reflexivity.
Qed.
Lemma stepacc_lui : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Lui rd imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_lui (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_lui; reflexivity.
Qed.
Lemma stepacc_auipc : forall segs regs pc mem rom w rd (imm : bv 20),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Auipc rd imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs
else regupd regs rd (v_auipc pc (Z.shiftl (bv_signed imm) 12)))
(v_addi pc 4) mem rom) []).
Proof.
intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_npc4, ?b_auipc; reflexivity.
Qed.
Lemma stepacc_jal_x0 : ltac2:(TCodec.tc2 tcn__NoReserveK "RJ'8'N%211&RHy5'U0yR0%211%5241';y8%611%311p061yQ0%:11yE%<11'B%:14&Q4r7r5%3221(2r2%22;1%93841'4&Q5r3%211(6%?3521'='RG'J%3221%M11&RCr4%211(<(RE(TNz(@%33Q;21%521B+4%84?>21%K2>1%Q23>;1'Q6'Q3'Q7%211%411&Q>r:&S;vT4r9r8r6%55432Q<1%8271(Q2(Q9&S7&U1%12QGO%3291%=5<;1QD9(:&Q8%211%93F41%;2F1%QM3F=1p0L1p0Q@1p0QG1pX@R21pZ<R51pYBR81pXJR91pY:R@1pY@R@1pYJRG1").
Proof.
intros segs regs pc mem rom w imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
rewrite is_x0_0; cbv beta iota.
rewrite b_addsext. reflexivity.
Qed.
Lemma stepacc_jalr_gen : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
(jalr_tgt (getr regs rs1) (bv_signed imm)) mem rom) []).
Proof.
intros segs regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
destruct (is_x0 rs1); cbv beta iota;
destruct (is_x0 rd); cbv beta iota;
rewrite ?b_jalr, ?b_npc4; reflexivity.
Qed.
Lemma stepacc_ecall : ltac2:(TCodec.tc2 tcn__NoReserveK "R<'8'N%211&RHy5'U0yR0%211%5241';y8%611%311p061yQ0%:11'B%812&Q4r6r4%3221(2r1%2291%93841'4&Q5r2%211(>%?3521'Q6'Q3'Q7%211%411&Q>r8&S;vT4r7r5%4532H1G%7261(Q2(Q9(Q1&S9%119&S:(TN+A(@%33QB21%52>1%Q22QA1(0%11QC&S8%11D%>8D<Q:531CQ9(:&Q8%211%C3O41%E2O1%QC3OG1p0Q51p0Q<1pZ<QG1pYBQJ1pXJQK1pY:R21pY@R21pYJR91").
Proof.
intros segs regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses.
cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses.
rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma stepacc_lbu : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned b)))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
assert (Hz : zext 64 (bv_extract 0 8 (le_bytes_to_word [b])) = Z_to_bv 64 (bv_unsigned b)).
{ rewrite le_word_1, b_extract8_id. apply bv_eq.
unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
pose proof (u8_range b). change (bv_modulus 64) with (2^64)%Z. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lb : forall segs regs pc mem rom w rd rs (imm : bv 12) b,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lb b))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 1%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm b Hfetch Hecall Hdecode Hread.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite b_lb_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lh : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lh v))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lh_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lhu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ2 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 2%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 2%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 16 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 16) with 65536%Z.
change (2 ^ (8 * Z.of_nat 2))%Z with 65536%Z in Hb. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lw : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v))
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_lwu : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ4 false rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 4%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : zext 64 (bv_extract 0 32 v) = v).
{ pose proof (rdn_length _ _ _ _ _ Hread) as Hlen.
pose proof (bytes_le_to_Z_bound bs) as Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite Hlen in Hb. rewrite Hv in Hb, Hnn.
apply bv_eq. unfold zext.
rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_small.
change (bv_modulus 32) with 4294967296%Z.
change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z in Hb. lia. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
Lemma stepacc_ld : forall segs regs pc mem rom w rd rs (imm : bv 12) bs v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
bytes_le_to_Z bs = bv_unsigned v ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom) =
MachineOk (@mkAccessReport machine_state
(mkst (if bv_eqb rd 0 then regs else regupd regs rd v)
(v_addi pc 4) mem rom)
[(v_addi (getr regs rs) (bv_signed imm), 8%nat)]).
Proof.
intros segs regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
assert (Hz : bv_extract 0 64 v = v).
{ apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r.
apply bv_wrap_bv_unsigned. }
stepacc_pipeline Hfetch Hecall Hdecode.
unfold getr; rewrite ?bv_eqb0_is_x0.
unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
rewrite (le_word_v _ _ Hv), Hz, b_npc4.
destruct (is_x0 rd); cbv beta iota;
reflexivity.
Qed.
End WithFP2.
