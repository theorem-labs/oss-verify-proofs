(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes NoReserveK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Scfg KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanCeil.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PlaceLemmasK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__AsanNodesMmLibK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AgentNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanCeil."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesMmLibK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesMmLibK.Nodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesMmLibK.OurSpecNodes2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlacement."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3SoundK.AX2SK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.BackingAlgebra."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.KitNodesS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PlaceLemmasK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "0C"; "0C'"; "1None"; "1O"; "1Some"; "1andb"; "1app"; "1bool"; "1cons"; "1false"; "1fst"; "1length"; "1list"; "1nat"; "1negb"]; ["1nil"; "1option"; "1orb"; "1pair"; "1prod"; "1snd"; "1true"; "1unit"; "2I"; "2and"; "2eq"; "2ex"; "2iff"; "2not"; "2or"; "3le"]; ["3lt"; "4Forall"; "4map"; "4nth"; "5Z"; "0E"; "0E'"; "0E1"; "0E2"; "0E3"; "0FS0"; "0FULL"; "0FULL'"; "0K"; "0KB"; "0LIMIT"]; ["6errno_ret_in"; "7Fs"; "8Segment"; "9MachineOk"; "9access_report"; "9fetch_word"; "9is_ecall"; "9machine_result"; "9machine_state"; "9memory_access"; "9mkAccessReport"; "9ms_gpr"; "9ms_svc_pending"; "9step_accesses"; ":mkCfg"; ":refusal_b"]; [":segments_reserved"; ":sys_input"; ";ENOMEM"; ";Model"; ";VmMaps"; ";alloc_top"; ";errno_ret"; ";event"; ";iv_subtract"; ";lazy_interior"; ";live_bytes"; ";m_fs"; ";m_halted"; ";m_vm_lazy"; ";m_vm_materialized"; ";m_vmmaps"]; [";map_contains"; ";map_has"; ";maps_subtract"; ";page_base"; ";page_in_ranges"; ";page_round_up_Z"; ";page_size"; ";region_free"; ";two_pow_64"; ";vm_add_lazy"; ";vm_backing_used"; ";vm_limit"; ";vm_maps"; ";vm_noaccess"; ";vm_reserved"; "<mmap_anon_b"]; ["<mmap_errnos"; "<mmap_fixed_noaccess_b"; "<mmap_fixed_rw_b"; "<mmap_flags_core"; "<mmap_modeled_b"; "<mmap_noaccess_b"; "<mmap_noreplace_noaccess_b"; "<mmap_noreplace_rw_b"; "<mmap_noreserve_b"; "<mmap_noreserve_backed_ok"; "<with_mmap_backing"; "=mprotect_budget_ok"; "=mprotect_errnos"; ">aluop"; ">mulop"; "?bvmap"]; ["0M"; "0M'"; "0P"; "0P'"; "0R"; "0R'"; "@epend"; "AA_bytes"; "AA_wf"; "AMInv"; "Aeager_used"; "Balloc_ceiling"; "Bbottomup_floor"; "Binit_sp_ok"; "DSlE"; "DSlF"]; ["DSlG"; "Dfixed_cs1"; "Dgrant_mem"; "Dgrant_post"; "Disp_facts"; "Dkind_lazy"; "Dkind_none"; "Dmaps_apart"; "Dnull_base"; "Dnull_cs1"; "Dnull_kfacts"; "Dnull_vhi"; "Dnull_vlo"; "Dsl_nn"; "Dslarm"; "Efixed_free_core"]; ["Casanreflect_fx"; "Fgap_weight"; "FkHighMemBeg"; "Fledger_split"; "GACS"; "GAM"; "GCEIL"; "GENOMEM_RET"; "GFLOOR"; "GKHI"; "GKRW"; "GKRWLAZY"; "GTOPC"; "Ga_abytes"; "Ga_brk"; "Ga_eager"]; ["Ga_fd"; "Ga_ghost"; "Ga_hlz"; "Ga_hna"; "Ga_maps"; "Ga_ss"; "Ga_tidset"; "Ga_totsz"; "Ga_vis"; "Ga_ylo"; "Gacs"; "Gadd_entry"; "Gam_base"; "Gam_kind"; "Gam_len"; "Gamap"]; ["Gamap_eqb"; "Gbudget_ok"; "Ge_sp0"; "Ge_stk_len"; "Ge_top"; "Gescale"; "Gexpr_vars_lt"; "Gfind_containing"; "Gfind_hole"; "Gfirst_run"; "Gfixed_args"; "Gflat_x"; "Gfresh_ok"; "Ggap_ok"; "Gimg_hi"; "Gimg_lo"]; ["Ginside_maps"; "Ginside_runs"; "Gis_ecall_at"; "Gis_fog"; "Gis_hole"; "Gis_tok_kind"; "Gkdisj_new"; "Gkimg_clip"; "Gkn"; "Gkn_grant_filter"; "Gkn_rezero"; "Gkn_unfill"; "Glit_ivs"; "Gmk_ss"; "Gmkind"; "Gmmap_len"]; ["Gno_fog"; "Gno_holes"; "Gnull_kend"; "Gnxt"; "Gpage_aligned"; "Gpage_up"; "Gpc"; "Grefuse"; "Greg"; "Grekind"; "Greplace_entry"; "Gsafe_range"; "Gsame_val"; "Gset_kn"; "Gshadow_facts"; "Gsr_vars_lt"]; ["Gunhole"; "Gvis_add"; "Gvis_cost"; "Gwith_maps0"; "Gwith_ss"; "Gzcdiv'"; "HMr"; "Hamap_den"; "Hcfg_of"; "Hcs_ok"; "Hext1"; "Hin_allow"; "Hin_hull"; "Hin_ivs"; "Hiv_disjoint"; "Hkimg_in_hull"]; ["Hmaps_match"; "Hseps"; "Hsum_sizes"; "HuE"; "Hutop"; "Hvis"; "IELit"; "IEVar"; "IKRange"; "IKWr"; "IKZero"; "ISA"; "Ialuop_eqb"; "Iedenot"; "Ienv"; "Iev"]; ["Iexpr"; "Iexpr_eqb"; "Ikentry"; "Imulop_eqb"; "Iranges_apart_x"; "Is_regs"; "Isplit_lit"; "Isr_upd"; "Itwo64"; "Ixhi"; "JelenZ"; "Jestart"; "Jkentry_ok"; "Jknow_ok"; "Jregs_ok"; "Kenv_agree"]; ["LB"; "LS"; "Lcovered"; "Lin_rng"; "Liv_wf"; "Livs_wf"; "Lmodel_ivs_wf"; "Loverlap_sum"; "Lsum_count"; "Mgrant_ok_na_pin"; "Nmmap_model"; "Nunfill"; "Nzfill"; "Oruns"; "Pgetr"; "Pmkst"]; ["Pregupd"; "Pseg_rom"; "Pv_addi"; "Qmprotect_model"; "Qnoaccess_model"; "RTSet"; "Rnode_ok"; "Ssrealizes"; "0SEGS"; "0SINV"; "TIn"; "Tfilter"; "Tflat_map"; "Tforallb"; "Uadd"; "Udiv"]; ["Ueqb"; "Ule"; "Uleb"; "Ult"; "Ultb"; "Umodulo"; "Umul"; "Uof_nat"; "Upow"; "Usub"; "0T"; "0TA"; "0Y"; "0a"; "0a'"; "0addr"]; ["0argH"; "0b"; "0b'"; "0base"; "0be"; "0ce"; "0cs"; "0cs'"; "0cs1"; "0cs2"; "0e"; "0ea"; "0eager"; "0extra"; "0f"; "0fhi"]; ["0flags"; "0flo"; "0fxg"; "0h"; "0hi"; "0ih"; "0iv"; "0k"; "0kd"; "0kinds"; "0knew"; "0l"; "0l1"; "0l2"; "0len"; "0lo"]; ["0m"; "0m'"; "0m0"; "0m1"; "0mem"; "0model"; "0model'"; "0ms"; "0ms'"; "0ms0"; "0n"; "0nZ"; "0nb"; "0ne"; "0nhi"; "0nlo"]; ["0nx'"; "0nx0"; "0o"; "0off"; "0p"; "0pc"; "0pcs"; "0prot"; "0q"; "0r"; "0regs"; "0rlo"; "0rn"; "0rom"; "0s"; "0scfg"]; ["0segs"; "0sr"; "0sr'"; "VBV"; "VZ_to_bv"; "Vbv"; "Vbv_unsigned"; "0sz"; "0top"; "0v"; "0vhi"; "0vlo"; "0w"; "0x"; "0x8"; "0ylo'"]; ["0z"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2K. Import AX2SK. Import APK. Import APSK.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition RES_hull_def (SEGS : list Segment) (A : APK.atable) : Prop :=
Forall (fun iv : word * word => img_lo A <= bv_unsigned (fst iv)
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
(segments_reserved SEGS).
Lemma in_ivs_covered : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'Q4'='D'\5yR0%211%4211%611'J'8&W=r2r1%3221&XB%1234%83731peH:1pi2B1").
Proof.
intros z l. unfold in_ivs, covered, in_iv, in_rng, B, S. reflexivity.
Qed.
Lemma in_ivs_cons : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'Q4'D'\5yR0%211%4211'=%112'J'8&W=r3(9r2r1%33:21%6251&B&6&YB&\6&;%13BB9%32D1%521=&YD&Y>&E%13HH?%92J1%4271%62D1%>281%G2FC%A221%K3JC1peHM1pe>Q01pi2Q61").
Proof. reflexivity. Qed.
Lemma in_ivs_app : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'Q4'='D'\5yR0%211%4211%611'J'8&W=r3&7r2r1%33921%6251&B%8275%9285%3221%=3<51peL?1peJ@1pi2H1").
Proof. intros. unfold in_ivs. apply existsb_app. Qed.
Lemma in_ivs_true' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'Q4'='D'\5yR0%211%4211%611&L'J'8&W=r2r1%3221(F%73621'K'I&Y:%13>78&YA&\6&;%13CC;%32E1r3%6221&YC&Y>&E%13JJB%:2L1%4281%6281%A281%B2@1qe>O1%E2Q01%O2G1peHQ11pi2Q91").
Proof.
intros z l. unfold in_ivs. rewrite existsb_exists. split.
- intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. eauto.
- intros [iv [Hin Hb]]. exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma in_ivs_false : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'Q4'='D'\5yR0%211%4211%611&L'J'8&W=r2r1%3221(:%73621&Y:%13<56&M'I&YA&\6&;%13CC<%32E1r4%6221&YC&Y>&E%13JJC%:2L1%4281%6281%?281%A11p0C1pe>Q01%O2G1peHQ11pi2Q91").
Proof.
intros z l. split.
- intros H iv Hin Hz. assert (T : in_ivs z l = true) by (apply (proj2 (in_ivs_true' z l)); eauto). congruence.
- intros H. destruct (in_ivs z l) eqn:E; [|reflexivity]. exfalso.
apply in_ivs_true' in E as [iv [Hin Hz]]. exact (H iv Hin Hz).
Qed.
Lemma sum_sizes_live : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "@'='D'\5yR0%211%4211%611'J'Q4&WBr1%211&R:%113%73631peH91").
Proof. induction l as [|[a s] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma sum_sizes_app : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "F'='D'\5yR0%211%4211%611'J'Q4&WB&7r2r1%33821%511&Y>%715%815%3221%<3;51peL>1peJ?1").
Proof. intros. rewrite !sum_sizes_live. apply live_bytes_app. Qed.
Lemma region_free_sem : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q<'='D'\5yR0%211%4211%611'Q4'J'8&RGr4r3r2%43321(F%83721&YCz&\6%12A8%4231'I&YAr5%62F1%321>&Y>%92IA%2241%=2B1%9251&W=r7%22G1(:%L3K21p061p0A1p0G1pi2Q11pfFQ51pf0Q61peHQ51").
Proof.
intros l lo n z Hrf Hn Hz. apply (proj2 (in_ivs_false z l)). intros [b s] Hin Hin2. cbn [fst snd] in Hin2.
pose proof (region_free_In l lo n b s Hrf Hin) as Hov. lia.
Qed.
Lemma region_free_app : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "J'='D'\5yR0%211%4211%611'J'8&RG&7r4r3%33821r2r1%73321&6%93743%:3754%3221%>3=51pfFB1pf0C1peLB1peJC1").
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma map_contains_intro : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q<'='D'\5yR0%211%4211%611&Y:(Cr2r1%347721r5%63821&YA&\6r3%22>1%32?6%5221&Y>r6%72C1%3215r4%:2F1%6219%=241'J'8&R@r8r7%3321<(F%73621p091p0B1p0I1pgNQ31pd4Q41pfFQ51pf0Q61peHQ51").
Proof.
intros l lo n b s Hin H1 H2. unfold map_contains. apply existsb_exists. exists (b, s). split; [exact Hin|].
cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma map_has_intro : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'='D'\5yR0%211%4211%611&Y:(Cr2r1%347721r3%63821'J'8&RAr4%23169(F%63521p081pfFB1pf0C1peHB1").
Proof.
intros l lo n Hin. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact Hin|].
cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.
Lemma eager_used_sem : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'R3&XFr1%211'J'Q4&SJr2%211&XH&?&XB&7'D'\5yR0%211%4211&RM&R?r3%211%411&R=%114%=3831%?21H%A11qhLG1&RL%;1G%211%G241%M3LI1p0O1pf2Q31").
Proof.
intros m Hwf. pose proof (vm_backing_used_sem m Hwf) as H. rewrite vm_backing_used_split in H. lia.
Qed.
Lemma mat_pages_le_A_bytes : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q2'='D'Q4%2211%411'R3'SIr2r1%3221&SHr3%211&YA&YF&YG&<'\5yR0%211&R>%11:%6231%811&RF%;221&SGr4%211%@241p0B1p0F1pf2K1p2M1").
Proof.
intros A m [N1 N2 N3 N4 N5] Hwf. apply allowed_pages_bound; assumption.
Qed.
Lemma vm_backing_used_le : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "L'='D'Q4%2211%411'R3'SIr2r1%3221&SHr3%211&YA&RJ%114&Y>&SJ%117&SGr4%211%6241%:281p0<1p0@1pf2E1p2G1").
Proof.
intros A m HM Hwf. rewrite vm_backing_used_split. pose proof (mat_pages_le_A_bytes A m HM Hwf). lia.
Qed.
Lemma vm_backing_used_limit : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'='D'Q4%2211%411'R3'SIr2r1%3221&SHr3%211&YA&RJ%114&RK&R?%117%311%7251p091p0=1pf2B1p2D1").
Proof.
intros A m HM Hwf. pose proof (vm_backing_used_le A m HM Hwf). pose proof (minv_budget _ _ HM). lia.
Qed.
Lemma sum_count_negb_covered_mono : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q5'='D'\5yR0%211%4211%611'Q4'J'8&XBr4r1%3221(F%73621r2%7261%:3914p041phL=1&YA&XH&?%11;qhLB1%421:r5%B21@%611qhLG1%921?%;261p0=1peHL1p6M1p4N1").
Proof.
intros C C' l H. apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. apply negb_true_iff.
destruct (covered C x) eqn:E; [|reflexivity]. rewrite (H x E) in Hx. discriminate.
Qed.
Lemma iv_subtract_pieces : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QA'\5yR0%211'Q4'D%1233&XD(Cr5r4%348821%511&Y:r2&R8r6r3%342981%63=51'I&YA&\6r7%22F1&;%13GG9%52I1%7241&Y>&E%13LL>%:2N1%4261%<2Q0B%62;1%?231'N%A25M%B2M<%3221%E251%F2>1p0H1p0Q01pgBQ71pe:Q:1pf0Q;1ph@Q=1pcLQ>1").
Proof.
intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.
Lemma maps_subtract_pieces : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QH'='D'\5yR0%211%4211%611'Q4&XEr4%211&Y:r2&RBr5r3%33271%63<51'K'Ir1r7%;3A21&YA&\6&;%13FF6%32H1%33HHC%52J1%7231&Y>&E%13MMH%:2O1%4261%43Q0Q0@%=2Q21%72;1%@241'Nr6%C271%D2M>%4221%J261%K2@1%L2I1qgDQ;1%O2Q<1p0Q11p0Q91pgBQ?1pe:Q>1pf0Q?1peHQA1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
- exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
- destruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.
Lemma iv_subtract_disjoint : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q?'\5yR0%211'Q4&YCr2r1%3221z&\6r4%22:1%8241'N&YA&Y>r6%82@1r5%:2B1%5231%721;r3%9216%;231'J'='D%12JJ%311&R8r7%241@>F(9(C%14Q1Q14C(@%119%53:31%>3:71p0@1p0M1p0Q31pe:Q81pf0Q91ph@Q;1pcLQ<1").
Proof.
intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
destruct Hd as [Hd|Hd].
- destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
- destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma maps_subtract_keeps : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q@'='D'\5yR0%211%4211%611'Q4&YCr2r1%3221z&\6r4%22<1%8241&Y:(Cr6r5%34AA21r7%63B21'N&YA&Y>%>2H5%?2I9%3221%521:%62A4%8221r8%@4NN1<&RBr9%231BA%E3Q141p071p0A1p0I1p0O1pe:Q41pf0Q51pgNQ91pd4Q:1peHQ91").
Proof.
induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
- injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
- right. apply IH; assumption.
Qed.
Lemma page_in_ranges_cons : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q8'\5yR0%211'D%1222'=%112'J'8&RDr3(9r2r1%33:21%6251&B&6&YB&\6&;%13CC9%32E1%42F=%6221&Y>&RF%2241&E%13KKA%;2M1%6291%>251%@291%I2HE%C221%M3LE1peHO1pe>Q21pg:Q51").
Proof. reflexivity. Qed.
Lemma page_in_ranges_app : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "H'\5yR0%211'='D%1233%311'J'8&RDr3&7r2r1%33921%6251&B%8275%9285%3221%=3<51peL?1peJ@1pg:E1").
Proof. intros. unfold page_in_ranges. apply existsb_app. Qed.
Lemma page_in_ranges_true : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q;'\5yR0%211'='D%1233%311&L'J'8&RDr2r1%3221(F%73621'K'I&Y:%13>78&YA&\6&;%13EE;%32G1r3%52I1%7231&Y>&RF%2241&E%13NND%<2Q01%62:1%?251%C291%D2B1qe>Q11%G2Q21%Q12I1peHQ31pg:Q81").
Proof.
intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
- intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
- intros (iv & Hin & H1 & H2). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma page_in_ranges_false : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q;'\5yR0%211'='D%1233%311&L'J'8&RDr2r1%3221(:%73621&Y:%13<56&M'I&YA&\6&;%13EE<%32G1r4%52I1%7231&Y>&RF%2241&E%13NNE%<2Q01%62:1%?251%A291%C11p0E1pe>Q21%Q12I1peHQ31pg:Q81").
Proof.
intros p l. split.
- intros H iv Hin Hc. assert (T : page_in_ranges p l = true) by (apply (proj2 (page_in_ranges_true p l)); exists iv; tauto). congruence.
- intros H. destruct (page_in_ranges p l) eqn:E; [|reflexivity]. exfalso.
apply page_in_ranges_true in E as (iv & Hin & H1 & H2). exact (H iv Hin (conj H1 H2)).
Qed.
Lemma page_in_ranges_covers : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'\5yR0%211'='D%1233%311'Q4'J'8&RDr3r2%3221(F%73621'I&YA&\6r4%22C1%4219&YC&Y>&RF%2251%42>1%;261&W=%12B:%F3E1@p041p0A1pi2J1peHL1pg:Q11").
Proof.
intros p l z Hp Hz. apply page_in_ranges_true in Hp as (iv & Hin & H1 & H2).
apply (proj2 (in_ivs_true' z l)). exists iv. split; [exact Hin | lia].
Qed.
Lemma page_in_ranges_subtract_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'\5yR0%211'='D%1233%311'Q4&XEr3%211&YAr2%2241'N&Y>&\6r6%22A1&RF%5221r4%;221%<2>5%:221'J'8&RDr7&RBr5%23>1:%5241%625@%93821p0;1p0G1p0K1pe:O1pf0Q01peHQ21pg:Q71").
Proof.
intros p l lo hi Hwf Hlh Hout. pose proof (u64_range p) as Rp. unfold page_size in *.
induction l as [|[a sz] l IH]; [reflexivity|].
apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract]. rewrite page_in_ranges_app, page_in_ranges_cons, (IH Hl). f_equal.
cbn [fst snd]. unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
unfold iv_subtract. rewrite page_in_ranges_app.
destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er];
cbn [page_in_ranges existsb fst snd app orb]; unfold page_size; rewrite ?u64_lit by lia; rewrite ?orb_false_r.
-
destruct Hout as [Hout|Hout].
+ destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
+ destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
-
destruct Hout as [Hout|Hout];
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + Z.min (bv_unsigned sz) (lo - bv_unsigned a)));
destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
-
destruct Hout as [Hout|Hout];
destruct (Z.leb_spec (Z.max (bv_unsigned a) hi) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (Z.max (bv_unsigned a) hi + (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)));
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
-
destruct Hout as [Hout|Hout];
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned sz)); cbn; try reflexivity; exfalso; lia.
Qed.
Lemma page_in_ranges_subtract_in : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q5'\5yR0%211'='D%1233%311'Q4&XEr3%211'I&YA&\6r5%22>1%4271&YCr2%2241%9241'J'8&RDr6&RBr4%23=1B%5241(:%93821p0;1p0F1pe:J1pf0K1peHM1pg:Q21").
Proof.
intros p l lo hi Hwf Hp. pose proof (u64_range p) as Rp.
destruct (page_in_ranges p (maps_subtract l lo hi)) eqn:E; [|reflexivity]. exfalso.
pose proof (page_in_ranges_covers p _ (bv_unsigned p) E ltac:(unfold page_size; lia)) as C.
rewrite in_ivs_covered in C.
destruct (maps_subtract_sem l lo hi Hwf ltac:(lia)) as (_ & _ & Cv). rewrite Cv in C.
apply andb_prop in C as [_ C]. apply negb_true_iff in C. unfold in_rng in C.
apply andb_false_iff in C as [C|C]; [apply Z.leb_gt in C | apply Z.ltb_ge in C]; lia.
Qed.
Lemma page_in_ranges_cons_in : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q6'\5yR0%211'='D%1233%311&YA&\6r3%2291r4%42;1%6231&Y>r5%82?1&RF%4221%5279%=221'J'8&RDr6(9(C%14II<@%33G1C%6251(F%:3921p0<1p0D1peHL1pfFQ11pcLQ21pg:Q31").
Proof.
intros p a n l H1 H2. rewrite page_in_ranges_cons. cbn [fst snd]. apply orb_true_iff. left.
apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.
Lemma page_in_ranges_cons_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q<'\5yR0%211'='D%1233%311'N&YA&Y>&\6r4%22;1&RF%5221r3%62?1%9231r2%92B1%;241%=219%?251&YCz%2219'J'8&RDr6(9(Cr5%24OO1F%43M1C%7261%827E%;3:21p0=1p0A1peHQ21pfFQ71pcLQ81pg:Q91").
Proof.
intros p a n l H Hn. rewrite page_in_ranges_cons. cbn [fst snd]. unfold page_size in *.
destruct (Z.leb_spec (bv_unsigned a) (bv_unsigned p)); destruct (Z.leb_spec (bv_unsigned p + 4096) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity. exfalso. lia.
Qed.
Lemma page_base_facts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "J'\5yR0%211'I&YA&\6&RCr1%211%4281%5293%7221&YC&Y>+TP0%2261%4261'J'Q4&YE%12;6z%53421%D271%E2=1pcLG1").
Proof.
intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma page_of_byte_in_aligned : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q5'\5yR0%211'Q4'J&YEr2+TP0%3221z%63721'I&YAr4&\6r5%22?1%5241&YCr3%2241%:241&RCr6%211%;2H1%>2;1&Y>%123E%A21@%C241p0:1p0F1p0G1pe:O1pf0Q01phLQ21").
Proof.
intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma page_of_byte_out_aligned : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q5'\5yR0%211'Q4'J&YEr2+TP0%3221z%63721'N&YC&\6r5%22>1r4%5221&YAr3%2215%:241&Y>&RCr6%211%=2I1%521D%:21>%;2=3%C221p0:1p0F1p0G1pe:O1pf0Q01phLQ21").
Proof.
intros x lo hi Hlo Hhi Hx. pose proof (page_base_facts x) as (P1 & P2 & P3).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma zfill_in : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'\5yR0%211'Ay8%511%311p051'I&YA&\6r4%22;1r1%42=1%6231&YC&Y>r3%92B1%3281%5271%>271'J&XLr5r2%342@91(5&\4z%22K1%42K1%:3K61p0<1phLQ11pf2M1pfFQ31pcLQ41").
Proof.
intros a n m x Hx. unfold zfill, zmem.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma unfill_in : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'\5yR0%211'Ay8%511%311p051'I&YA&\6r4%22;1r1%42=1%6231&YC&Y>r3%92B1%3281%5271%>271'J&XKr5r2%342@91(3%11H%73H31p091phLN1pf2J1pfFQ01pcLQ11").
Proof.
intros a n m x Hx. unfold unfill.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma mrestrict_at : forall (H : word -> bool) M (x : word),
mrestrict H M x = if H x then None else M x.
Proof. reflexivity. Qed.
Lemma v_addi_pc : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'Q4&YAzr1%3221&YC&Y>r2+4%3221&YH+2+R0%3221%9251'J'\5yR0%211&Y2&\4r3%2251%421?%B23@%5281%;3831p0=1p0H1pg:M1").
Proof. intros p H0 H4. unfold v_addi. rewrite u64_lit by lia. reflexivity. Qed.
Lemma is_ecall_at_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QF'='QB%211'U:'J'8&V2r2r1%3221(F%73621'K'\5yQ0%211'I'A%113&QEr4&\4yR0&VFr3%211%5241%8271(5%12>E%J3<31&QF%11H%M3L1G&YAz%221;&YC&Y>+4%22?1&YH+2+R0%3221%8251%N2:1%O2>1%Q02B1qhJQ21%Q62Q31p0Q81pd>QA1pbBQC1").
Proof.
intros SEGS cs H. unfold is_ecall_at in H.
apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
exists w. unfold two64 in H4. auto.
Qed.
Lemma page_up_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'Q4'J&VEr1%211&RE%113%63731peN81").
Proof. intros. unfold page_up, page_round_up_Z, page_size. f_equal. f_equal. lia. Qed.
Lemma env_agree_le' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'>'WN&X?r3r2r1%43321'Or5r4%3221r6%:3139p031p081pR>>1pR<?1pd6A1pd4B1").
Proof. intros b b' E E' [H1 H2] Hle. split; [|exact H2]. intros n Hn. apply H1. lia. Qed.
Lemma env_agree_refl' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "8'>'WN&X?r2r1%33211pR<51pd471").
Proof. intros. split; [intros; reflexivity | reflexivity]. Qed.
Lemma env_agree_trans' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "A'>'WN&X?r4r3r2%43321r5%63143r6%83136p031p061pRD<1pRB=1pR@>1pd4@1").
Proof. intros b E1 E2 E3 [A1 B1] [A2 B2]. split; [intros n Hn; rewrite A1 by lia; apply A2; lia | congruence]. Qed.
Lemma ext1_agree'' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'WN'>'\5yR0%211&X?r2r3&W:r1%23341%63541pcL81phD<1pR<>1").
Proof.
intros E v a. split; [|reflexivity]. intros n Hn. cbn [ext1 ev].
destruct (Nat.eqb_spec n v); [lia | reflexivity].
Qed.
Lemma nth_sr_vars_lt' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'>'='X0%211'J'8&VOr3r2%3221(F%73621&Q0uQ0%2261&UFr5&Q3r4(WFz%211%54D?41%8271%D3C1>p0;1p0?1pgDK1ph4I1pd4M1").
Proof.
intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
cbn [APK.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.
Lemma elenZ_lit'' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'WN'Q4'I&YAzr1%3221&YC&YH+2+R0%3221%5271%;271'J&X:r3(WFr2%211%5241%73D13p091pi2F1pR<H1").
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma aluop_eqb_refl : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'S='J'8&WLr1%2211(F%63521pg681").
Proof. intros []; reflexivity. Qed.
Lemma mulop_eqb_refl : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'S>'J'8&X3r1%2211(F%63521pg681").
Proof. intros []; reflexivity. Qed.
Lemma expr_eqb_refl : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'X0'J'8&X1r1%2211(F%63521pdF81").
Proof.
induction e; cbn; rewrite ?aluop_eqb_refl, ?mulop_eqb_refl, ?IHe1, ?IHe2, ?IHe, ?Z.eqb_refl, ?Nat.eqb_refl, ?Bool.eqb_reflx; reflexivity.
Qed.
Lemma amap_eqb_refl : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'U?'J'8&U@r1%2211(F%63521pf281").
Proof. intros [b l k]. unfold amap_eqb. cbn. rewrite !expr_eqb_refl. destruct k; reflexivity. Qed.
Lemma seps_filter : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "D'D'\5yR0%211%4211'8p021'=%114'WAr1%211&Y;r3r2%33;21%711p061peH:1pdN=1").
Proof.
intros f l H. induction H as [|p l Hf Hl IH]; cbn; [constructor|].
destruct (f p); [|exact IH]. constructor; [|exact IH].
apply Forall_forall. intros q Hq. apply filter_In in Hq as [Hq _]. exact (proj1 (Forall_forall _ _) Hf q Hq).
Qed.
Lemma sum_sizes_filter_le : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "D'D'\5yR0%211%4211'8p021'=%114&YA&WB&Y;r2r1%33:21%511%613%8221peH:1pdN=1").
Proof.
intros f l. induction l as [|[b s] l IH]; cbn; [lia|]. pose proof (u64_range s). destruct (f (b, s)); cbn; lia.
Qed.
Lemma A_bytes_app' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'='D'Q4%2211%411'J&SG&7r2r1%33721%511&Y>%715%815%3221%;3>51peL=1peJ>1").
Proof. intros l1 l2. induction l1; cbn [A_bytes app]; [lia|]. rewrite IHl1. lia. Qed.
Lemma A_bytes_flat_map_split : forall {T} (f : T -> list (Z * Z)) (g : T -> bool) l r,
A_bytes (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) = A_bytes (flat_map f (l ++ r)).
Proof.
intros T f g l r. rewrite !flat_map_app, !A_bytes_app'. induction l as [|x l IH]; cbn; [lia|].
destruct (g x); cbn; rewrite !A_bytes_app'; lia.
Qed.
Lemma in_flat_map_split : forall {T U} (f : T -> list U) (g : T -> bool) l r y,
In y (flat_map f (List.filter g l ++ (List.filter (fun x => negb (g x)) l ++ r))) <-> In y (flat_map f (l ++ r)).
Proof.
intros T U f g l r y. rewrite !in_flat_map. split.
- intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|].
apply in_app_iff in Hx as [Hx|Hx]; [apply filter_In in Hx as [Hx _]; apply in_app_iff; left; exact Hx|]. apply in_app_iff; right; exact Hx.
- intros (x & Hx & Hy). exists x. split; [|exact Hy]. apply in_app_iff in Hx as [Hx|Hx].
+ destruct (g x) eqn:E; [apply in_app_iff; left; apply filter_In; auto|].
apply in_app_iff; right. apply in_app_iff; left. apply filter_In. rewrite E. auto.
+ apply in_app_iff; right. apply in_app_iff; right. exact Hx.
Qed.
Lemma sum_count_filter_le : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QG'Q4'8p021'D'\5yR0%211%4211p017'=%113&Y:r1r2%33721'Jr4%114(F%43B21'I&YA&X@%117%321<&YC&Y>&XA%11<%3261%52B1%;271r8%11Dr9%11F%E3Q331p061phLQ61p0D1p0J1pgBQ21&XH&Y;r3%23Q61Q0%42N1r5%621Q3%L231p091peHQ91pdNQ<1pW8QC1pW6QD1").
Proof.
intros P P' f l H. induction l as [|q l IH]; cbn; [lia|].
assert (IH' := IH ltac:(intros q' Hq'; apply H; right; exact Hq')).
destruct (f q) eqn:E; cbn; [|unfold iv_count in *; pose proof (zcount_nonneg P (B q) (Z.to_nat (S q))); lia].
unfold iv_count in *. rewrite (zcount_ext P' P); [lia|].
intros x Hx. apply (H q (or_introl eq_refl) E). pose proof (S_range q). rewrite Z2Nat.id in Hx by lia. lia.
Qed.
Lemma filter_map_ext : forall {T U} (h : T -> U) (f : U -> bool) (f' : T -> bool) l,
(forall x, In x l -> f (h x) = f' x) -> List.filter f (map h l) = map h (List.filter f' l).
Proof.
intros T U h f f' l H. induction l as [|x l IH]; cbn; [reflexivity|].
rewrite (H x (or_introl eq_refl)). rewrite (IH ltac:(intros y Hy; apply H; right; exact Hy)).
destruct (f' x); reflexivity.
Qed.
Lemma mmap_flags_core_22 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'J'Q4&S3&\4yR0+Q2%3221%511%83713"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_32 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "9'J'Q4&S3&\4yR0+QB%3221%511%83713"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4022 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'Q4&S3&\4yR0+`Q2%3221%511+Q2%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_4032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'Q4&S3&\4yR0+`QB%3221%511+QB%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_22 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+Q2%3221%511(:%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_32 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+QB%3221%511(:%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4022 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+`Q2%3221%511(F%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_4032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+`QB%3221%511(F%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_104022 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'Q4&S3&\4yR0+QP`Q2%3221%511+QPPQ2%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_flags_core_104032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'Q4&S3&\4yR0+QP`QB%3221%511+QPPQB%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+QP`Q2%3221%511(F%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ":'J'8&S8&\4yR0+QP`QB%3221%511(F%93821"). Proof. vm_compute. reflexivity. Qed.
Lemma with_mmap_backing_plain : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "F'\5yR0%211'R3'J'8&S8r4%211(:%63521&S:r5r3r2%443821%<3=12p071pf2?1pfFA1pcLB1pe2C1").
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.
Lemma with_mmap_backing_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "H'\5yR0%211'R3'J'8&S8r4%211(F%63521&S:r5r3r2%443821&RI%13:43%>3?31p091pf2A1pfFC1pcLD1pe2E1").
Proof. intros flags a n m H. unfold with_mmap_backing. now rewrite H. Qed.
Lemma with_mmap_backing_halted : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "E'\5yR0%211'R3'J'A%114&R<&S:r4r3r2r1%544321%711%813%<3:21pf2>1pfF@1pcLA1pe2B1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma with_mmap_backing_fs : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "D'\5yR0%211'R3'J&QA&R;&S:r4r3r2r1%544321%711%813%;3:21pf2=1pfF?1pcL@1pe2A1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma with_mmap_backing_vmmaps : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "D'\5yR0%211'R3'J'R4&R?&S:r4r3r2r1%544321%711%813%;3:21pf2=1pfF?1pcL@1pe2A1").
Proof. intros. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); reflexivity. Qed.
Lemma mmap_gates_core34 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q0'\5yR0%211'J'Q4&S3r1%211+Q2%63521'I'8&S4&\4+3%22>1r2z%52A1%73431(F%B3:21%:3464(:%E3=21&S5%138:8%H3@17%B241%C281p0E1pe2M1").
Proof.
intros flags Hc. unfold mmap_modeled_b, mmap_noaccess_b. rewrite Hc.
repeat split; vm_compute; reflexivity.
Qed.
Lemma mmap_gates_core50 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q9'\5yR0%211'J'Q4&S3r2%211+QB%63521'I'8&S4r3&\4z%22?1%53;41(:%@3821&S5%13?85%C3;14&S1%138;8(F%G3?21+3%>2K1%631@=%K3C1<&S2%134C@%N3F18%H241%I291%J2>1%K2B1p0M1pg@Q51pe2Q61").
Proof.
intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
rewrite Hc. repeat split; try (vm_compute; reflexivity).
all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.
Lemma region_free_not_contains : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q0'='D'\5yR0%211%4211%611&YCz&\6r1%2281%5241'J'8&RGr4r3r2%43321(F%83721&R@r5%23187(:%=3<21p061p0@1pfFI1pf0J1peHI1").
Proof.
intros l lo n Hn Hfree. unfold map_contains.
apply Bool.not_true_iff_false. intros H. apply existsb_exists in H as ([b s] & Hin & H).
cbn [fst snd] in H. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (State.region_free_In _ _ _ _ _ Hfree Hin) as Hov.
unfold iv_overlap in Hov. apply andb_false_iff in Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.
Lemma mmap_errnos_ENOMEM : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ";'Q4&Y:r1&S0%33421'Jr2&R2%33821p051pdF:1").
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma mprotect_errnos_ENOMEM : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ";'Q4&Y:r1&S<%33421'Jr2&R2%33821p051pdF:1").
Proof. intros e [<-|[]]. reflexivity. Qed.
Lemma errno_ret_ENOMEM : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ">'J'\5yR0%211&R6&R2%211&\4&YI&X8+<%3221%52:1%=3:71").
Proof. apply bv_eq. reflexivity. Qed.
Section OurSpecNodes.
Context {fxg : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma stepacc_ecall_epend : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R1&S?y5'\5yR0%211%5241'Ay8%611%311p061yQ0%:11'J%812&QEv\0r4%3221(5r1%2291%93841'8&QFr2%211(F%?3521'QG'QD'QH%211%411&QM&XOvZBr7r6r5%554321G%72I1(QC(QJ&SF&XN(\3+A(H%33Q@21%52=1%76?>=<Q21(@&QI%211%<3H41%>2H1%Q<3H@1p0N1p0Q51phJQ@1pgLQC1pf:QD1pg<QK1pgFQK1").
Proof.
intros regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
reflexivity.
Qed.
Lemma node_instr_noacc : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QE'QH'R3'J'A'\5yR0%211%411&R<r2%211(3%116%;3631&QLr4%211%?3:15'QG'QD%11D%311&QMv\0r5%3221(QC(QJr3(@&QI%211%53Q041%72=1%Q03=91&Y6v[O(QNr6%221?'G'R7%=11q031%72D6q051%;6G:7631p0=1p0O1p0Q41pfBQB1pf<QB1pf@QD1").
Proof.
intros ms model ms' Hh Hsvc Hstep.
assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
{ unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
rewrite materialize_model_accesses_nil. reflexivity. }
apply (node_ok_of_pnode_instr segs scfg); [exact Hsvc |].
split.
- intros []. apply (sstep_instr segs ms model ms' model Hh Hsvc Hacc).
- intros e st Hss. exists tt.
inversion Hss; subst;
match goal with
| H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
| H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
end.
Qed.
Lemma srz_sys_lazy : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R8&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11&Y5'J%:1<&R<r3%211(3%11A%73631%A1:&QEv\0r7%3221(5%12@;%?3731'8&QFr4%211(F%E3521'Y7v[O(QN&SFvZBr:r9r8&XN(\3+A(H%33Q@21%5281%;6:987I1r6%>221%A4M@1E&XOr;%25@1?>=%C21Q0r5%G4Q3F21p071p0J1p0Q11p0Q:1pcFQC1phJQE1pf<QH1pgLQJ1pf:QK1pg<R21pgFR21").
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply srz_silent1; [| exact Hc].
apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.
Lemma epend_len : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QO&S?y5'\5yR0%211%5241'Ay8%611%311p061'Q4'J&XNr5(\3+;(H%33A21%6251&\4r1%22C1%;3C41'I&YCzr2%3221&YH+2+R0%3221%8261%:261&\6&QK&SFvZBr7r6r4+A%L3Q:1J%O251%86765O41u1%;221%=2Q=1r3%Q63Q721&M%Q02QAJ%Q93QA61%311%O251p0F1p0Q21peNQ?1pgLQA1pf:QB1pg<QI1pgFQI1").
Proof.
intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
- apply u64_lit. lia.
- intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.
Lemma srz_node1 : forall c (IB : Type) (nx : IB -> config) (B : TSet) (b0 : IB),
ShapeAlg.node_ok segs scfg c IB (fun _ => []) nx ->
(forall i, srealizes segs scfg (nx i) B) ->
srealizes segs scfg c B.
Proof.
intros c IB nx B b0 Hnode HB.
assert (HB0 : B []) by (eapply srealizes_nonempty; apply (HB b0)).
apply (srz_conseq segs scfg c (t_alt (fun i : IB => t_emit [] B))).
- apply (srz_node segs scfg c IB (fun _ => []) nx (fun _ => B) b0 Hnode). exact HB.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq B HB0 tr) Hi).
+ intros H. exists b0. exact (proj2 (t_emit_nil_eq B HB0 tr) H).
Qed.
Lemma refusal_b_mmap_epend : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'QH'\5yR0%211'R3'J'Q4&\6r3%2271+VN%63521'8&QO&R1v\0r5r4%43321r2%732<1&Q@&S0%2214%C3<41p0>1pgDG1pf<G1phNI1pf@M1").
Proof. intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.
Lemma mmap_rw_check : forall ms x8 model eff flags,
bv_unsigned x8 = 222%Z ->
ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 3 ->
ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if grant_ok_na_pin model r nZ && mmap_noreserve_backed_ok flags model nZ
&& listNN_eqb zs [(r, Z_to_bv 64 nZ)]
then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (mmap_model r (Z_to_bv 64 nZ) model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
destruct (mmap_gates_core34 flags Hcore) as (Gm & _ & _).
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm. cbn [negb]. cbv beta iota zeta. fold nZ.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
destruct (errno_ret_in mmap_errnos r); [reflexivity|].
unfold grant_ok_na_pin, mmap_model.
destruct (mmap_noreserve_backed_ok flags model nZ); rewrite ?andb_true_r, ?andb_false_r; [reflexivity|].
cbn [andb]. reflexivity.
Qed.
Lemma srz_mmap_rw1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "U=&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11'Q4&Y5'J%;14&QEv\0r8%3221(5r4%22;1%93841'8&QFr5%211(F%?3521%J1L&R<r7%211(3%11Q1%F3631&XNr<(\3+A(H%33Q;21%6251&\4+VN%22Q=1%Q13Q=41r=+;%;3QC19%>231%82QCD%Q73QC21'I&YCz%221Q7&YH+2+R0%3221%72Q<1%9261r?+<%K3R31I%N231+3%I2R41%QH3R431r@+=%Q23R:1Q0%Q5231r9%QN3R:21&S3r:%211+Q2%R33R521rB+>%Q=3RE1Q;%Q@231-1%Q;2RF1%R:3RF31rC+?%QD3RL1QB%QG231%QA2RLQ5%R@3RL21&REr>%211r1%QG2S21'K&XIr3%23>51%RJ3R@1R<qcLS71%62S81&S9%13Q5C6%RO3RE1RArE%:31=RE%S23RH1RD'Y7v[O(QN&XOvZB&Y0rJ+:%RB3SJ1R@r2%53421&Y2rI+4%3221&XLrH%238S81rG%@5?9521&S:&XJrF%23>S>1%44Q@?S?1%G261%J4SJI1QIp0L1pcLT;1%J5IA=;7%L21Q1rA%Q04T0O21p051p0Q61p0Q:1tfFTCQB1tfHT:QE1p0QI1p0R01p0R81p0R>1p0RE1p0RM1p0S81p0S?1p0SK1p0T31p0T:1pRNTE1pe2U11peNTH1phJTJ1pf<TM1pgLTO1pf:U01pg<U71pgFU71").
Proof.
intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) Hb0 HB.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
pose proof (fun eff => mmap_rw_check ms (getr regs 17) model eff flags Hno Hne1
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
rewrite Hb0 in Hchk.
assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [(a, n)] [] [] [] end).
pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (mmap_model a n model) end).
assert (HokS : forall a, grant_ok_na_pin model a nZ = true ->
check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [(a, n)] [] [] []) model
= CheckOk (with_mmap_backing flags a n (mmap_model a n model)) []).
{ intros a Ha. rewrite Hchk. rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros [a Ha]; cbn [effs ms']. exact (HokS a Ha).
+ intros [a Ha]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mmap_errnos r) eqn:Er.
* exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
* rewrite Hchk in Hc. rewrite Er in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
destruct (listNN_eqb zs [(r, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
exists (exist _ r Hg). repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; discriminate.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
destruct (grant_ok_na_pin model r nZ && true && listNN_eqb zs [(r, n)])%bool; [|discriminate].
injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
+ intros [a Ha]; reflexivity.
- intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. apply HB. exact Ha.
Qed.
Lemma mmap_none_check : forall ms x8 model eff flags,
bv_unsigned x8 = 222%Z ->
ms_gpr ms 1 <> Z_to_bv 64 0 -> ms_gpr ms 2 = Z_to_bv 64 0 ->
ms_gpr ms 3 = flags -> mmap_flags_core flags = 34%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z (bv_unsigned (ms_gpr ms 1)) in
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if grant_ok_na_pin model r nZ && listNN_eqb us [(r, Z_to_bv 64 nZ)]
then CheckOk (with_mmap_backing flags r (Z_to_bv 64 nZ) (noaccess_model r (Z_to_bv 64 nZ) model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags Hno H1 H2 H3 Hcore H4 H5 nZ.
destruct (mmap_gates_core34 flags Hcore) as (_ & Gm & Gn).
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
rewrite E1, H2, H3, H5, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn. cbn [negb]. cbv beta iota zeta. fold nZ.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
destruct (errno_ret_in mmap_errnos r); [reflexivity|].
unfold grant_ok_na_pin, noaccess_model. reflexivity.
Qed.
Lemma srz_mmap_none1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "U7&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11'Q4&Y5'J%;14&QEv\0r8%3221(5r4%22;1%93841'8&QFr5%211(F%?3521%J1L&R<r7%211(3%11Q1%F3631&XNr<(\3+A(H%33Q;21%6251&\4+VN%22Q=1%Q13Q=41r=+;%;3QC19%>231%82QCD%Q73QC21'I&YCz%221Q7&YH+2+R0%3221%72Q<1%9261r?+<%K3R31I%N231%H2R3<%QG3R321r@+=%Q13R91O%Q4231r9%QM3R921&S3r:%211+Q2%R23R421rB+>%Q<3RD1Q:%Q?231-1%Q:2RE1%R93RE31rC+?%QC3RK1QA%QF231%R>3RJ1H&REr>%211r1%QE2S01'K&XIr3%23=51%RH3R>1R:qcLS51%62S61rD%731:RE%RM3RC1R?'Y7v[O(QN&XOvZB&Y0rI+:%R=3SE1R;r2%53421&Y2rH+4%3221&XKrG%238S81rF%@5?9521&S:&Y4rE%23>S>1%44QC?S?1%G261rA%K4SFJ21p0M1pcLT71%K5JB><8%M21Q2%Q04SKO1R6p041p0Q61tfFT=Q>1tfHT4QA1p0QE1p0QK1p0R31p0R91p0R@1p0RG1p0S21p0S91p0SE1p0SM1p0T41pRNT?1pe2TK1peNTB1phJTD1pf<TG1pgLTI1pf:TJ1pg<U11pgFU11").
Proof.
intros regs pc mem rom model w len flags KB HF HE Hh H17 H11 Hlen H12 H13 Hcore H14 H15 nZ n (a0 & Ha0) HB.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
destruct (epend_len regs pc mem rom len H11 Hlen) as [Hl1 Hne1]. fold ms in Hl1, Hne1.
pose proof (fun eff => mmap_none_check ms (getr regs 17) model eff flags Hno Hne1
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13) Hcore
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)) as Hchk.
cbv zeta in Hchk. rewrite Hl1 in Hchk. fold nZ n in Hchk.
assert (Hn0 : (0 <= nZ)%Z) by (unfold nZ; apply page_round_up_Z_nonneg; lia).
pose (IB := {a : word | grant_ok_na_pin model a nZ = true}).
pose (effs := fun i : IB => match i with exist _ a _ => mkEffectU a [] [] [(a, n)] [] [] end).
pose (ms' := fun i : IB => match i with exist _ a _ => with_mmap_backing flags a n (noaccess_model a n model) end).
assert (HokS : forall a, grant_ok_na_pin model a nZ = true ->
check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU a [] [] [(a, n)] [] []) model
= CheckOk (with_mmap_backing flags a n (noaccess_model a n model)) []).
{ intros a Ha. rewrite Hchk. rewrite (grant_na_pin_not_errno model a nZ Hn0 Ha), Ha. cbn [andb].
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
eapply (srz_node1 (mkCfg ms model) IB (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB (exist _ a0 Ha0)).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) IB effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros [a Ha]; cbn [effs ms']. exact (HokS a Ha).
+ intros [a Ha]; cbn [effs ms']. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno).
exact (grant_na_pin_not_errno model a nZ Hn0 Ha).
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mmap_errnos r) eqn:Er.
* exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) (HokS a0 Ha0)).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact (grant_na_pin_not_errno model a0 nZ Hn0 Ha0).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend _ _ _ _ Hno). exact Er.
* rewrite Hchk in Hc. rewrite Er in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (grant_ok_na_pin model r nZ) eqn:Hg; [|discriminate]. cbn [andb] in Hc.
destruct (listNN_eqb us [(r, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst us. injection Hc as <- <-.
exists (exist _ r Hg). repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; discriminate.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
destruct (grant_ok_na_pin model r nZ && listNN_eqb us [(r, n)])%bool; [|discriminate].
injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
+ intros [a Ha]; reflexivity.
- intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.
End OurSpecNodes.
Section OurSpecNodes2.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma refusal_b_mprotect_epend : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'QH'\5yR0%211'R3'J'Q4&\6r3%2271+W2%63521'8&QO&R1v\0r5r4%43321r2%732<1&Q@&S<%2214%C3<41p0>1pgDG1pf<G1phNI1pf@M1").
Proof. intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity. Qed.
Lemma mmap_fixed_gate_open : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R@'R4'\5yR0%211'Q4'J&YE&\6r2%2271&RF%5221z%83921&YCr3%92>1%3251%4263&YA&Y>r5%?2D1&REr4%211%6241&SK%9221&SMr7%211'I'8&YB&RH%M2Q26r6%?11%C231%6251(:%Q53921&?&R5r8%211%=281%511%Q<3@18&Y@%Q=2?Q9%221Q8%:11%QA3E1=&YD%12Q<D%>11%QE3I1A&YH+2+R0%3221%QA2J1%QB2QDJ%QC2K3%Q2221%Q3241%Q42:1%Q52?1%Q62E1%Q72M1p0Q91p0Q=1p0QH1p0QJ1p0QO1peNR91pd0R;1pe8R?1").
Proof.
intros h addr len Hal Hpos Hlen Hce Hisp. pose proof alloc_ceiling_val.
pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr).
repeat split.
- apply Z.leb_gt. unfold two_pow_64. lia.
- rewrite (proj2 (Z.leb_le _ _) (alloc_top_ge_of_ceiling _ _ Hisp Hce)). reflexivity.
- rewrite (proj2 (Z.eqb_eq _ _) Hal). reflexivity.
- rewrite (proj2 (Z.ltb_lt _ _) Hpos). reflexivity.
- lia. - lia. - lia.
Qed.
Lemma mmap_fixed_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
destruct (mmap_gates_core50 flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & _ & Gfn & Gfr).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn, Gfr. cbn [negb]. cbv beta iota zeta.
rewrite G1, G2, G3, G4. fold nZ. fold n.
assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
{ apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
rewrite Hmc, andb_false_r, Hrf.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
unfold mmap_model. reflexivity.
Qed.
Lemma mmap_gates_noreplace : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QI'\5yR0%211'N'J'Q4&S3r2%211+QPPQ2%63521+QPPQB%83741%:231'I'8&S4r3&\4z%22C1%53>41(:%C3821&S5%13B85%F3;14&S1%13E;8%I3>17&S2%13H>;%L3A1:&S6%13>A>(F%Q03E21+3%D2Q51%631FC%Q43I1B&S7%134IF%Q73L18&RO%11L%Q:3O1;%Q1241%Q2281%Q32=1%Q42B1%Q52F1%Q62J1%Q72N1p0Q91pg@QE1pe2QF1").
Proof.
intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b,
mmap_noreplace_noaccess_b, mmap_noreplace_rw_b, mmap_noreplace_flags_b.
destruct Hc as [Hc|Hc]; rewrite Hc; (repeat split; try (vm_compute; reflexivity));
try (destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity);
(apply (mmap_anon_b_of_core flags _ Hc); reflexivity).
Qed.
Lemma mmap_noreplace_rw_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
ms_gpr ms 2 = Z_to_bv 64 3 -> ms_gpr ms 3 = flags ->
(mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
destruct (mmap_gates_noreplace flags (Z_to_bv 64 3) Hcore) as (Gm & Gn & Gfn & Gfr & _ & Gnn & Gnr & Ga).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn, Gnr. cbn [negb]. cbv beta iota zeta.
rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct us; [|destruct (errno_ret_in mmap_errnos r); [destruct zs|]; reflexivity].
destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
unfold mmap_model. reflexivity.
Qed.
Lemma srz_mmap_fixed_rw_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 222 ->
(0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
(forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb zs [(addr, n)] && mmap_noreserve_backed_ok flags model nZ
then CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []
else CheckReject
| _ => CheckReject
end) ->
mmap_noreserve_backed_ok flags model nZ = true ->
srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (zfill addr n mem) rom)
(with_mmap_backing flags addr n (mmap_model addr n model))) KB ->
srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk Hbk HB.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
rewrite Hbk in Hchk.
assert (Hna : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
pose (effs := fun _ : unit => mkEffectU addr [] [(addr, n)] [] [] []).
pose (ms' := fun _ : unit => with_mmap_backing flags addr n (mmap_model addr n model)).
assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [(addr, n)] [] [] []) model
= CheckOk (with_mmap_backing flags addr n (mmap_model addr n model)) []).
{ rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros []; exact HokS.
+ intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mmap_errnos r) eqn:Er.
* exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
* rewrite Hchk, Er in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r zs. cbn [andb] in Hc. injection Hc as <- <-.
exists tt. repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; discriminate.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
destruct (bv_eqb r addr && listNN_eqb zs [(addr, n)] && true)%bool; [|discriminate].
injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold mmap_model. rewrite with_vmmaps_halted. exact Hh.
+ intros []; reflexivity.
- intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.
Lemma mmap_fixed_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags -> mmap_flags_core flags = 50%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
destruct (mmap_gates_core50 flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & _ & _).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl), Gm, Gn, Gfn. cbn [negb]. cbv beta iota zeta.
rewrite G1, G2, G3, G4. fold nZ. fold n.
assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = false).
{ apply region_free_not_contains; [unfold n; rewrite u64_lit by lia; lia|].
rewrite RefNodes.region_free_app in Hrf. apply andb_true_iff in Hrf. tauto. }
rewrite Hmc, andb_false_r, Hrf.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct zs; [|reflexivity].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
unfold noaccess_model. reflexivity.
Qed.
Lemma mmap_noreplace_none_free_check : forall ms x8 model eff flags (addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z -> init_sp_ok (m_vmmaps model) ->
ms_gpr ms 2 = Z_to_bv 64 0 -> ms_gpr ms 3 = flags ->
(mmap_flags_core flags = 1048610 \/ mmap_flags_core flags = 1048626)%Z ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) addr n = true ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms x8 model eff flags addr len Hno H0 Hal Hpos H1 Hlen Hce Hisp H2 H3 Hcore H4 H5 nZ n Hrf.
destruct (mmap_fixed_gate_open (m_vmmaps model) addr len Hal Hpos Hlen Hce Hisp) as (G1 & G2 & G3 & G4 & Hlen' & HnZ).
destruct (mmap_gates_noreplace flags (Z_to_bv 64 0) Hcore) as (Gm & Gn & Gfn & Gfr & Gnn & _ & _ & Ga).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
rewrite Hu1 in E. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
rewrite E1, H2, H3, H5, H0, Hu1, mmap_off_aligned_b_0, Ga, Gm, Gn, Gfn, Gfr, Gnn. cbn [negb]. cbv beta iota zeta.
rewrite G1, G2, G3, G4. fold nZ. fold n. rewrite Hrf.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct zs; [|reflexivity].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); [destruct us|]; reflexivity].
unfold noaccess_model. reflexivity.
Qed.
Lemma srz_mmap_fixed_none_free1 : forall regs (pc : word) mem rom model w (addr : word) (len : Z) (flags : word) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 222 ->
(0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len <= alloc_ceiling)%Z ->
let nZ := page_round_up_Z len in let n := Z_to_bv 64 nZ in
(forall eff, check_syscall (sys_input segs (epend regs pc mem rom (getr regs 17)) (getr regs 17)) eff model
= match eff with
| mkEffectU r [] [] us [] [] =>
if errno_ret_in mmap_errnos r
then match us with [] => CheckOk model [] | _ => CheckReject end
else if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []
else CheckReject
| _ => CheckReject
end) ->
srealizes segs scfg (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) rom)
(with_mmap_backing flags addr n (noaccess_model addr n model))) KB ->
srealizes segs scfg (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hnw nZ n Hchk HB.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)). fold ms in Hchk.
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hna : errno_ret_in mmap_errnos addr = false).
{ apply errno_ret_in_below; [reflexivity|]. pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof alloc_ceiling_val. unfold two_pow_64. lia. }
pose (effs := fun _ : unit => mkEffectU addr [] [] [(addr, n)] [] []).
pose (ms' := fun _ : unit => with_mmap_backing flags addr n (noaccess_model addr n model)).
assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU addr [] [] [(addr, n)] [] []) model
= CheckOk (with_mmap_backing flags addr n (noaccess_model addr n model)) []).
{ rewrite Hchk, Hna, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros []; exact HokS.
+ intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mmap_errnos r) eqn:Er.
* exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Hna.
-- cbn [eff_ret]. rewrite (refusal_b_mmap_epend segs _ _ _ _ Hno). exact Er.
* rewrite Hchk, Er in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst r us. cbn [andb] in Hc. injection Hc as <- <-.
exists tt. repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; discriminate.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct ci; [|destruct (errno_ret_in mmap_errnos r); destruct us; discriminate].
destruct (errno_ret_in mmap_errnos r); [destruct us; [|discriminate]; injection Hc as <- <-; exact Hh|].
destruct (bv_eqb r addr && listNN_eqb us [(addr, n)])%bool; [|discriminate].
injection Hc as <- <-. rewrite with_mmap_backing_halted. unfold noaccess_model. rewrite with_vmmaps_halted. exact Hh.
+ intros []; reflexivity.
- intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_unmaps1_epend. exact HB.
Qed.
Lemma srz_mprotect1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "U1&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11'Q4&Y5'J%;14&QEv\0r8%3221(5r4%22;1%93841'8&QFr5%211(F%?3521%J1L&R<r7%211(3%11Q1%F3631&XNr<(\3+A(H%33Q;21%6251&\4+W2%22Q=1%Q13Q=41r=+:%;3QC19%>231%Q63QB1D&YE&\6%12QFQ5&RF%4221z%Q=3Q?21r?+;%G3QO1E%J231%D2QOQ>%QC3QO21&YCr9%22:1&Y>r;%A2R61&REr:%211%6241&RH%;221rB+<%Q93RA1Q7%Q<231+3%Q72RB1%R63RB31%=1Q?%Q:2RE1&R@&RM&R?r@%211%411r>r1%83321%RB3R81R4&RLrA%:11%311r2%?32Q:1%RI3R?1R;&S;r3%23L@1%RM3RC1R?'Y7v[O(QN&XO&T@&Y0rG%R72SBQI%332R21&Y2rF+4%3221&XLrE%23IS61rD%>5=9521&Y3rC%23NS;1%C241%F4SAE1R6rH%E5D1B>:%G219%J4SEI1Q<p051p0M1p0Q21p0Q:1tfFT9QE1p0QH1p0R01p0R:1p0R>1p0RE1p0RM1p0S31p0S?1p0SG1p0SN1pRNT91peNT;1pd0TF1phJT>1pf<TA1pgLTC1pf:TD1pg<TK1pgFTK1").
Proof.
intros regs pc mem rom model w addr len KB HF HE Hh H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HB.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
cbv zeta in Hchk. fold n in Hchk. rewrite Hbud in Hchk.
assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by reflexivity.
pose (effs := fun _ : unit => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []).
pose (ms' := fun _ : unit => mprotect_model addr n model).
assert (HokS : check_syscall (sys_input segs ms (getr regs 17)) (mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] []) model
= CheckOk (mprotect_model addr n model) []).
{ rewrite Hchk, Hz. unfold w_is0. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity. }
eapply (srz_node1 segs scfg (mkCfg ms model) unit (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KB tt).
- apply (node_chk_ev_gen_noacc segs scfg ms model (getr regs 17) unit effs ms' (fun _ => []) materialize_model_accesses_nil Hh eq_refl).
+ intros []; exact HokS.
+ intros []; cbv delta [effs] beta iota. apply alloc_nonrefusal_step. cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
+ intros [r ws zs us cs ci] m' evs Hc Hu.
destruct (errno_ret_in mprotect_errnos r) eqn:Er.
* exfalso. apply Hu. apply (alloc_refusal_unforced segs scfg Halloc ms model (getr regs 17) _ _ _ _ ltac:(rewrite Hno; reflexivity) HokS).
-- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Hz.
-- cbn [eff_ret]. rewrite (refusal_b_mprotect_epend _ _ _ _ Hno). exact Er.
* rewrite Hchk, Er in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
cbn [andb] in Hc. destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. injection Hc as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r.
exists tt. repeat split; reflexivity.
+ intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; discriminate.
+ intros [r ws zs us cs ci] m' evs Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mprotect_errnos r); [destruct zs; [|discriminate]; injection Hc as <- <-; exact Hh|].
cbn [andb] in Hc. destruct (w_is0 r && listNN_eqb zs [(addr, n)])%bool; [|discriminate].
injection Hc as <- <-. unfold mprotect_model. rewrite with_vmmaps_halted. exact Hh.
+ intros []; reflexivity.
- intros []. cbv delta [effs ms'] beta iota. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.
Definition fixed_free_core (c : Z) : Prop := (c = 50 \/ (c = 1048610 \/ c = 1048626))%Z.
Lemma srz_mmap_fixed_rw_free1R : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "V5&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11'Q4&Y5'J%;14&QEv\0r9%3221(5r5%22;1%93841'8&QFr6%211(F%?3521%J1L&R<r8%211(3%11Q1%F3631&XNr=(\3+A(H%33Q;21%6251&\4+VN%22Q=1%Q13Q=41r>+:%;3QC19%>231%Q63QB1D&YE&\6%12QFQ5&RF%4221z%Q=3Q?21&YCr:%82QM1%3251rA+;%K3R31I%N231%H2R37%QG3R321r;%;2=1&YA&Y>%D2R9Q4&REr<%211%5241&SK%8221&SM&R?r@%211%411rE+<%QA3RI1Q?%QD231+3%Q?2RJ1%R>3RJ31rF+=%QH3S01QF%QK231%RC3RO1QA&T?&S3r?%211%411rH+>%R23S:1R0%R5231-1%R02S;1%RO3S;31rI+?%R93SA1R7%R<231%R62SAQH%S53SA21rC%Q:11r1%R;2SF1&RG&7'D%12SISI&RN%Q;1F%211&RL%113%83631%:31Q5<%SE3S;1S7&S9r3%23Q@H1%SI3S?1S;'Y7v[O(QN&XO&T@&Y0rN%231RMQ8&Y2rM+4%3221&XLrL%23Q?A1rK%=5<9521&S:&XJrJ%23QEG1%44R0QFH1%D261%G4T>F1R9rO%F5E1C@<%H21;%K4TBJ1R6p051p0N1p0Q31tfFU5Q@1tfHTLQC1p0QF1p0QM1p0R51p0R;1p0RA1p0RI1p0RO1p0S91p0S<1p0SC1p0SH1p0T01p0T61p0TB1p0TJ1p0U11pRNU<1pe2UH1peNU?1pd0UJ1phJUB1pf<UE1pgLUG1pf:UH1pg<UO1pgFUO1").
Proof.
intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf Hbk HB.
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
eapply (srz_mmap_fixed_rw_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact Hbk|exact HB].
intros eff. destruct Hcore as [Hc|Hc].
- apply (mmap_fixed_rw_free_check _ _ model eff flags addr len Hno);
rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
- apply (mmap_noreplace_rw_free_check _ _ model eff flags addr len Hno);
rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.
Lemma srz_mmap_fixed_none_free1R : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "V0&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3yQ0%;11'Q4&Y5'J%;14&QEv\0r9%3221(5r5%22;1%93841'8&QFr6%211(F%?3521%J1L&R<r8%211(3%11Q1%F3631&XNr=(\3+A(H%33Q;21%6251&\4+VN%22Q=1%Q13Q=41r>+:%;3QC19%>231%Q63QB1D&YE&\6%12QFQ5&RF%4221z%Q=3Q?21&YCr:%82QM1%3251rA+;%K3R31I%N231%H2R37%QG3R321r;%;2=1&YA&Y>%D2R9Q4&REr<%211%5241&SK%8221&SM&R?r@%211%411rE+<%QA3RI1Q?%QD231%Q>2RIQ0%R=3RI21rF+=%QG3RO1QE%QJ231%RB3RN1Q@&T?&S3r?%211%411rH+>%R13S91QO%R4231-1%QO2S:1%RN3S:31rI+?%R83S@1R6%R;231%S33S?1GrC%Q811r1%R92SD1&RG&7'D%12SGSG&RN%Q91E%211&RL%113%83631%:31Q4<%SC3S91S5'Y7v[O(QN&XO&T@&Y0rMrG%332RH1&Y2rL+4%3221&XKr2rK%33921rJ%?5>:621&S:&Y4%13>7Q:%34R2?81%E251rD%I4T:H21rN%H5G1EA<%J21;%M4T>L1R9p051p0Q01tfFU0Q=1tfHTGQ@1p0QC1p0QI1p0R11p0R71p0R=1p0RD1p0RJ1p0S41p0S71p0S>1p0SC1p0SK1p0T11p0T=1p0TE1p0TL1pRNU71pe2UC1peNU:1pd0UE1phJU=1pf<U@1pgLUB1pf:UC1pg<UJ1pgFUJ1").
Proof.
intros regs pc mem rom model w addr len flags KB HF HE Hh H17 H10 Hal Hpos H11 Hlen Hce Hisp H12 H13 Hcore H14 H15 nZ n Hrf HB.
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
eapply (srz_mmap_fixed_none_free1 regs pc mem rom model w addr len flags KB HF HE Hh H17 Hlen Hce); [|exact HB].
intros eff. destruct Hcore as [Hc|Hc].
- apply (mmap_fixed_none_free_check _ _ model eff flags addr len Hno);
rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
- apply (mmap_noreplace_none_free_check _ _ model eff flags addr len Hno);
rewrite ?ms_gpr_epend0, ?ms_gpr_epend1, ?ms_gpr_epend2, ?ms_gpr_epend3, ?ms_gpr_epend4, ?ms_gpr_epend5; try assumption.
Qed.
Lemma fixed_free_core_32 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "8&T?&S3&\4yR0+QB%3221%511%711"). Proof. left. apply mmap_flags_core_32. Qed.
Lemma fixed_free_core_4032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "8&T?&S3&\4yR0+`QB%3221%511%711"). Proof. left. apply mmap_flags_core_4032. Qed.
Lemma fixed_free_core_104022 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "8&T?&S3&\4yR0+QP`Q2%3221%511%711"). Proof. right. left. apply mmap_flags_core_104022. Qed.
Lemma fixed_free_core_104032 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "8&T?&S3&\4yR0+QP`QB%3221%511%711"). Proof. right. right. apply mmap_flags_core_104032. Qed.
End OurSpecNodes2.
Lemma page_base_aligned' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'\5yR0%211'J'Q4&YE&\6r1%2271+TP0%5221z%93821&RCr2%211%=3>12p051pg:@1").
Proof.
intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite u64_lit; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma iv_subtract_contained : forall (a sz : word) lo hi,
bv_unsigned a <= lo -> hi <= bv_unsigned a + bv_unsigned sz -> lo <= hi ->
iv_subtract a sz lo hi
= (if bv_unsigned a <? lo then [(a, Z_to_bv 64 (lo - bv_unsigned a))] else [])
++ (if hi <? bv_unsigned a + bv_unsigned sz then [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))] else []).
Proof.
intros a sz lo hi H1 H2 H3. unfold iv_subtract.
rewrite Z.min_r by lia. rewrite Z.max_r by lia. reflexivity.
Qed.
Lemma map_replace_entry : forall (f : amap -> word * word) l m pcs,
map f (replace_entry l m pcs) = flat_map (fun m' => if amap_eqb m' m then map f pcs else [f m']) l.
Proof.
intros f l m pcs. unfold replace_entry. rewrite flat_map_concat_map, concat_map, map_map, <- flat_map_concat_map.
apply flat_map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.
Lemma maps_subtract_map_replace : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R9'U?'D'\5yR0%211%4211p061'=%118'Q4&Y:r1r6%33=21'J'8&U@r2%2216(:%63521%>1@&R8&;r9r3%211%43GG1&E%13II3r5r4%:45321(9(@%11N%33O:1%G3@51p0B1p0J1pf4Q81r7%Q03Q:O1%K2J2(F%O3N21r:%11F%I3Q<Q<1%E3Q=Q=2%L421Q6D&Q2%14QDQ?6;%Q73Q031p091p0=1pf4QH1&RBr8%84QKQF1B%331MQ3&VJ%13EQBQ0%<4QOQJ51%QB3Q;41p091p0J1pe:QJ1pf0QK1pg>QM1pf2R61peHQO1pdNR21").
Proof.
intros f l m pcs lo hi Hout Hin. rewrite map_replace_entry.
induction l as [|m' l IH]; [reflexivity|]. cbn [map flat_map maps_subtract].
destruct (f m') as [a sz] eqn:Ef. cbn [maps_subtract].
rewrite (IH ltac:(intros x Hx; apply Hout; right; exact Hx) ltac:(intros x Hx; apply Hin; right; exact Hx)). f_equal.
destruct (amap_eqb m' m) eqn:Heq.
- rewrite <- (Hin m' (or_introl eq_refl) Heq), Ef. reflexivity.
- pose proof (Hout m' (or_introl eq_refl) Heq) as X. rewrite Ef in X. cbn [fst snd] in X. exact X.
Qed.
Lemma in_replace_entry : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "M'='U?%211&Y:r1&VJr4r3r2%43321%73961'N'Ir5%;3=61&M'J%13@9;%311%7251%A3C>7%B3D=>%:221%<241p0>1pf4H1pg>H1pf2J1peHJ1").
Proof.
intros l m pcs m' H. unfold replace_entry in H. apply in_flat_map in H as (m0 & Hm0 & Hin).
destruct (amap_eqb m0 m) eqn:He.
- apply APSK.amap_eqb_eq in He. subst m0. right. auto.
- destruct Hin as [<-|[]]. left. split; [exact Hm0|]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.
Lemma maps_subtract_in_pieces : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q0'='D'\5yR0%211%4211%611'Q4&Y:(Cr5r4%348821r6%63921r2&R8r3%245871%;3>41&RBr8%231<;%?3B61p051p0;1pgBE1pe:D1pf0E1pgNI1pd4J1peHI1").
Proof.
induction l as [|[a sz] l IH]; intros b s lo hi q Hin Hq; [destruct Hin|].
cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
- injection Heq as -> ->. left. exact Hq.
- right. eapply IH; eassumption.
Qed.
Lemma seps_app_intro : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'='D'\5yR0%211%4211%611'WAr2%211&Y:r6%23741&W>r4r3%3221p051p061pgB>1pg:?1&7r5%23B19%A11p051p0A1p0B1peLF1peJG1").
Proof.
induction l1 as [|p l1 IH]; intros l2 H1 H2 H12; [exact H2|].
inversion H1 as [|p' l' Hf Hl]; subst. cbn [app]. constructor.
- apply Forall_app. split; [exact Hf|]. apply Forall_forall. intros q Hq. apply H12; [left; reflexivity | exact Hq].
- apply IH; [exact Hl | exact H2 |]. intros a b Ha Hb. apply H12; [right; exact Ha | exact Hb].
Qed.
Lemma seps_iv_subtract : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'\5yR0%211'Q4&XD(Cr4r3%346621%511&YAr2%2251'WA&R8r6r5%3421;:%511p071p0;1pe:B1pf0C1ph@E1pcLF1").
Proof.
intros a sz lo hi Hwf Hlh. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
assert (S1 : forall p : word * word, seps [p]) by (intros p; apply seps_cons; [apply Forall_nil | apply seps_nil]).
destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app];
try apply S1; try apply seps_nil.
apply seps_cons; [|apply S1]. apply Forall_cons; [|apply Forall_nil].
unfold iv_disjoint. cbn [fst snd]. rewrite !u64_lit by lia. left. lia.
Qed.
Lemma seps_maps_subtract : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "K'='D'\5yR0%211%4211%611'Q4'WAr3%211&XEr4%211&YA%1236&RBr6r5%33217%<11p061p091p0=1pe:A1pf0B1peHD1").
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hs Hwf Hlh; [constructor|].
apply ivs_wf_cons_inv in Hwf as [Ha Hl]. inversion Hs as [|p' l' Hf Htl]; subst.
cbn [maps_subtract]. apply seps_app_intro; [apply seps_iv_subtract; assumption | apply IH; assumption |].
intros p q Hp Hq.
destruct (iv_subtract_pieces a sz lo hi p Ha Hp) as (P1 & P2 & P3).
destruct (maps_subtract_pieces l lo hi q Hl Hq) as (r & Hr & Q1 & Q2 & Q3).
pose proof (proj1 (Forall_forall _ _) Hf r Hr) as D. unfold iv_disjoint in *. cbn [fst snd] in *. lia.
Qed.
Lemma iv_subtract_bounds : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R?'\5yR0%211'Q4'D%1233'J&YEr5+TP0%3221z%63921&YC&\6r8%22?1%4261r:%52B1%=21;%?3B1:&YAr7r<%;2H1%4231&Y>r=%?2L1%3215%9218&YH+2+R0%3221%>2E1&Y:r;&R8r?r>%3421>B%63Q651'I&E%13Q<Q<F%Q12Q>1%Q32Q51&;%13Q@Q@J%Q52QB1%Q=21Q;%Q?3QB1Q:%Q?27Q=%QA3QD1Q<%Q22B5%N26:%Q421Q8%?231%@251%A281%B2>1p0D1p0L1p0Q21p0Q81p0Q>1p0Q?1p0QD1p0QJ1p0QK1pd<R51pe<R61pgBR51pe:R81pf0R91ph@R;1pcLR<1").
Proof.
intros a sz lo hi q ih ce Hlo Hhi Hsz Hal Hszl Hih Hce Hce64 Hq.
pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
unfold iv_subtract in Hq. apply in_app_iff in Hq as [Hq|Hq].
- destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
rewrite u64_lit by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct (Z.le_gt_cases (bv_unsigned sz) (lo - bv_unsigned a)); [rewrite Z.min_l by lia | rewrite Z.min_r by lia]; repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [fst snd].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
destruct (Z.le_gt_cases hi (bv_unsigned a)); [rewrite !Z.max_l by lia | rewrite !Z.max_r by lia]; rewrite !u64_lit by lia; repeat split; try lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma maps_subtract_bounds : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R8'='D'\5yR0%211%4211%611'Q4'J&YEr4+TP0%3221z%63721&YAr3&YH+2+R0%3221%6251'Q1'I&YC&\6&Er1%23HH1%42J1%62A1&;%13LL5%82N1%I21G%K3L1F%K27I%M3N1Hr6%H216&Y>%128<r5%L221%E251%F281%G2;1%H2A1qe>Q;1r8%L3Q=21r7%Q521C%Q62<?%O221%Q02B1%Q12E1%Q22K1qe>QE1&RBr9%231<:%Q83QI41p0=1p0Q;1p0QC1p0QD1pd<QL1pe<QM1pe:QN1pf0QO1peHR11").
Proof.
induction l as [|[a sz] l IH]; intros lo hi ih ce Hlo Hhi Hce HB; [constructor|].
apply Forall_cons_iff in HB as [(B1 & B2 & B3 & B4 & B5) HBl]. cbn [fst snd] in B1, B2, B3, B4, B5.
cbn [maps_subtract]. apply Forall_app. split; [|apply IH; assumption].
apply Forall_forall. intros q Hq. exact (iv_subtract_bounds a sz lo hi q ih ce Hlo Hhi B1 B2 B3 B4 B5 Hce Hq).
Qed.
Lemma sum_sizes_maps_subtract_le : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "K'='D'\5yR0%211%4211%611'Q4&XEr3%211&YAr2%2241&WB&RBr5r4%33219%511%614%:221p091p0=1pe:A1pf0B1peHD1").
Proof.
intros l lo hi Hwf Hlh. rewrite !sum_sizes_live, !live_bytes_sum_count.
rewrite (proj1 (proj2 (maps_subtract_sem l lo hi Hwf Hlh))). apply sum_count_mono. intros; reflexivity.
Qed.
Lemma ledger_split_maps_subtract : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "L'='D'\5yR0%211%4211%611'Q4&XEr5%211&TCr6r3r2%43321&RBr7%23169r4%93217p061p0<1pcJ@1pRLA1pe:B1pf0C1peHE1").
Proof.
intros l lo hi K Y Hwf H b s Hin. destruct (maps_subtract_pieces l lo hi (b, s) Hwf Hin) as ([b' s'] & Hr & R1 & R2 & _).
cbn [fst snd] in R1, R2. destruct (H b' s' Hr); lia.
Qed.
Lemma replace_entry_notin : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "B'='U?%211&M&Y:r2r3%33621%511'J&VJr4%23167%43;12p061pg>=1pf2?1pf@?1").
Proof.
intros ms m pcs H. induction ms as [|h t IH]; [reflexivity|]. unfold replace_entry in *. cbn [flat_map].
destruct (amap_eqb h m) eqn:He.
- apply APSK.amap_eqb_eq in He. subst h. exfalso. apply H. left. reflexivity.
- cbn [app]. f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.
Lemma maps_subtract_disjoint_id : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q>'='D'\5yR0%211%4211%611'Q4&YCr2r1%3221&Y:r5%23941'Iz&\6&E%13??:%32A1%=251'N&YA&Y>&;%13FFA%:2H1%4218%621@r4%8214%:231%B2<1p0D1pe>N1'J&RBr3%23J91%43Q21Kp061p0O1pe:Q41pf0Q51peHQ71").
Proof.
intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|]. cbn [maps_subtract].
destruct (H (a, sz) (or_introl eq_refl)) as [P D]. cbn [fst snd] in P, D.
rewrite (iv_subtract_disjoint a sz lo hi Hlh P D). cbn [app]. f_equal. apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.
Lemma maps_match_app_pcs : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'WN'='U?%211'D'\5yR0%211%4211%811&Y:r1r4%33;21'J'8&V3r2%211(:%63521p081pg<D1&W@r5r3%33219r6&7%13K5A&Q2&W7%115%34OI19%63J19%<3861p0:1p0?1peHM1pf@Q41pg>Q51pR<Q91").
Proof.
intros E pcs ms l Hpf HM. induction pcs as [|pc pcs IH]; [exact HM|]. cbn [app map maps_match].
rewrite (Hpf pc (or_introl eq_refl)). exists (map (amap_den E) pcs ++ l). split; [reflexivity|].
apply IH. intros x Hx. apply Hpf. right. exact Hx.
Qed.
Lemma maps_match_subtract : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "S8'WN'='U?%211'D'\5yR0%211%4211%811'Q4&W@r7r6r5%43321'WA%114&Y:r1r8%33=21&YCz&\6&Er2%23DD1%42F1%7261p091pe>G1r9%?3OE1'J'8&V3%11A(:%53421%B2LK&YA&WMr=&U<r:%211%5241%H2Q:1%821M&Y>r>r;%911%<231%O2QA1&U>%115%@271%Q32QE1%:251%D2Q91&Q2&W7r?%211%44R0QJ1>&R8r<%I11%L261%?13%N281%6431LQ9%Q83R181%QI3R9QHQ0%Q81QB%Q;3Q:1Q7p031pg<R=1rA&VJr@%231Q0Q8&RB%13EAQ1%R;3631p081p0>1p0L1p0Q91p0QC1p0QE1p0QL1p0QO1p0R>1p0RA1pe:RG1pf0RH1pg>S01pf2S21peHRL1pf@S31pR<S71").
Proof.
intros E ms. induction ms as [|h t IH]; intros l m pcs lo hi HM Hs Hpos Hm Hf Hlh Hc1 Hc2 Hpcs Hpf; [destruct Hm|].
cbn [maps_match] in HM. unfold replace_entry. cbn [flat_map]. fold (replace_entry t m pcs).
destruct (is_fog h) eqn:Hfh.
- assert (He : amap_eqb h m = false).
{ destruct (amap_eqb h m) eqn:He; [|reflexivity]. apply APSK.amap_eqb_eq in He. subst h. congruence. }
rewrite He. cbn [app maps_match]. rewrite Hfh.
assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
destruct HM as [HM | ([a sz] & l' & -> & Hsz & HM)].
+ left. eapply IH; eassumption.
+ right. inversion Hs as [|p l0 Hfa Hl]; subst. cbn [maps_subtract].
pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
rewrite (iv_subtract_disjoint a sz lo hi Hlh (Hpos (a, sz) (or_introl eq_refl)) ltac:(lia)). cbn [app].
exists (a, sz), (maps_subtract l' lo hi). split; [reflexivity|]. split; [exact Hsz|].
eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
- destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
unfold amap_den at 1. cbn [maps_subtract].
destruct (amap_eqb h m) eqn:He.
+ apply APSK.amap_eqb_eq in He. subst h.
assert (Hnot : ~ In m t).
{ intros Hmt. pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
pose proof (Hpos (amap_den E m) (or_introl eq_refl)) as P. unfold iv_disjoint, amap_den in D, P. cbn [fst snd] in D, P. lia. }
rewrite (replace_entry_notin t m pcs Hnot). rewrite <- Hpcs.
rewrite (maps_subtract_disjoint_id l' lo hi Hlh).
2:{ intros iv Hiv. split; [apply Hpos; right; exact Hiv|].
pose proof (proj1 (Forall_forall _ _) Hfa iv Hiv) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. lia. }
apply maps_match_app_pcs; [exact Hpf | exact HM].
+ assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [rewrite amap_eqb_refl in He; discriminate | exact Hm]).
pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hmt Hf)) as D.
unfold iv_disjoint, amap_den in D. cbn [fst snd] in D.
pose proof (Hpos _ (or_introl eq_refl)) as P. unfold amap_den in P. cbn [snd] in P.
rewrite (iv_subtract_disjoint (edenot E (am_base h)) (edenot E (am_len h)) lo hi Hlh P ltac:(lia)). cbn [app maps_match]. rewrite Hfh.
exists (maps_subtract l' lo hi). split; [reflexivity|].
eapply IH; try eassumption. intros iv Hiv. apply Hpos. right. exact Hiv.
Qed.
Definition hull_lt (A : atable) : Prop := img_lo A < img_hi A.
Section Nodes.
Variable SEGS : list Segment.
Variable scfg : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat. Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool. Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
(segments_reserved SEGS).
Hypothesis HULL_ok : hull_ok A. Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis e_sp0_init : expr_vars_lt nx0 e_sp0 = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis HULL_tiled : forall z, img_lo A <= z < img_hi A -> in_ivs z (segments_reserved SEGS) = true.
#[local] Notation CSOK := (APSK.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APSK.hid A argH).
#[local] Notation VIS := (APSK.vis A).
#[local] Notation MR := (APSK.Mr A argH).
#[local] Notation ALLOW := (APSK.allowA A).
#[local] Notation cfg := (cfg_of SEGS).
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.
Let reg_sound' := APSK.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APSK.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APSK.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APSK.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APSK.regs_ok_set_n.
Let in_ivs_map_den' := APSK.in_ivs_map_den.
Let kimg_clip_in_hull' := APSK.kimg_clip_in_hull A.
Let cs_ok_agree' := APSK.cs_ok_agree SEGS A nx0 LIMIT SINV argH e_sp0_init argH_agree SINV_agree FS0.
Let cs_ok_frame' := APSK.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APSK.hid_agree A nx0 argH e_sp0_init argH_agree.
Let vis_add_sound' := APSK.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_high FS0 0%nat.
Let A_wf_allowA' := APSK.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APSK.know_ok_unhide SEGS A.
Let hid_hull' := APSK.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APSK.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APSK.maps_match_exact nx0 HS XN XE XB.
Lemma mmap_len_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "SB'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'X0'Q4'W9vY8v0vQ?vY9vZ0vQ:r8r7r6r5r4%<;;:987654321'J'D%12A@%221A%I11&V?%11<(5(Cr3%24IH<1r2%44:J21%62:1%>3:81&\6&WMr:&VHr9u;%3221%6251%82Q?1'I&XN&\4+;%22QF1%42:1r1%52QG1%Q03QG31&YCz%2215&YH+2+R0%3221%72:1%A261r;%K21Q?&RE%11?%D2R61%Q?3R641%?2>QC&YA%12QE5%226QE%L221&YE+TP0%22:1%QH3R61F%Q72?Q5%Q:2L1r<%Q<213%QM3RD31%Q>2QCR4r=%Q@21R6%R13RH31p051pR>S01%Q<2<1%Q=2A1%Q>2F1%Q?2H1%Q@2O1%QA2Q91teNRHQC1p0QM1p0R=1pfNRK1pg0RL1pfLRN1pf<S01pRHS21pW:S81pd>S?1pR<SA1").
Proof.
intros E cs R FULL model ne nlo nhi HC HML len.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (reg_sound' E cs R FULL model 11 HC ltac:(lia)) as R11. change (Z.of_nat 11) with 11 in R11.
pose proof (u64_range (edenot E (reg cs 11))) as Hr.
rewrite mmap_len_eq in HML. unfold mmap_len_ref in HML.
destruct (reg_lit cs 11) as [lz|] eqn:H11.
- destruct (Z.ltb_spec 0 lz); [|discriminate]. injection HML as <- <- <-.
destruct (reg_lit_sound' E cs R FULL model 11 lz HC ltac:(lia) H11) as [R11' Hlz]. change (Z.of_nat 11) with 11 in R11'.
assert (Hlen : len = lz).
{ unfold len. rewrite <- R11, R11'. apply u64_lit. unfold two64 in Hlz. lia. }
rewrite Hlen. pose proof (page_round_up_Z_bounds lz ltac:(lia)) as PB. unfold page_size in PB.
rewrite page_up_eq.
split; [exact R11'|]. split; [unfold two64 in Hlz; lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [apply page_round_up_Z_aligned'|]. intros E' _. reflexivity.
- destruct (xlo (kn cs) (reg cs 11)) as [lo|] eqn:Hxl; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [hi|] eqn:Hxh; [|discriminate].
match type of HML with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
injection HML as <- <- <-.
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hlo Hal].
apply Z.ltb_lt in Hlo. apply Z.leb_le in Hal. apply Z.leb_le in Hhi.
pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hxl) as B1.
pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hxh) as B2.
destruct (ealign_sound SEGS E _ (kn cs) (reg cs 11) HK) as [_ Hdiv].
assert (Hmod : len mod 4096 = 0).
{ unfold len. destruct Hdiv as [q Hq]. rewrite Hq.
replace (2 ^ ealign (kn cs) (reg cs 11)) with (2 ^ (ealign (kn cs) (reg cs 11) - 12) * 4096)
by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
assert (Hpr : page_round_up_Z len = len).
{ unfold page_round_up_Z, page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold len in *. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
rewrite Hpr.
split; [rewrite R11; symmetry; apply Z_to_bv_bv_unsigned|].
split; [unfold len in *; lia|]. split; [symmetry; apply Z_to_bv_bv_unsigned|].
split; [lia|]. split; [unfold len in *; lia|]. split; [exact Hmod|].
intros E' HE'. exact HE'.
Qed.
Lemma bv5_of_nat : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "A'>&Q0r1uQ0%3221'J'\5y5%211&\4&YGr2%211%4261%93611p0;1pfF@1"). Proof. reflexivity. Qed.
Lemma bv5_10 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+:(H%33521/015&\4&YGu:%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_11 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+;(H%33521/015&\4&YGu;%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_12 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+<(H%33521/015&\4&YGu<%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_13 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+=(H%33521/015&\4&YGu=%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_14 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+>(H%33521/015&\4&YGu>%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_15 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+?(H%33521/015&\4&YGu?%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma bv5_17 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'J'\5y5%211(\3+A(H%33521/015&\4&YGuA%211%42;1%>3;61"). Proof. apply bv_eq. reflexivity. Qed.
Lemma some_inj : forall {T} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. injection H as H1. exact H1. Qed.
Lemma CEIL_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "5'J'Q4&SK&TF%43321").
Proof. reflexivity. Qed.
Lemma KHI_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "5'J'Q4&TB&TI%43321").
Proof. reflexivity. Qed.
Lemma FLOOR_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "5'J'Q4&SL&TH%43321").
Proof. rewrite bottomup_floor_val. reflexivity. Qed.
Lemma Z_to_bv64_m1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'Q4'Jr1&YI&X8+1%3221%63751'\5yR0%211&\4r2%2241-1%4261%?3631p0:1pf8B1").
Proof. intros m1 ->. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma reserved_free_above : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'R3'\5yR0%211'J'='D%1244%311&RN&R?r3%211%411&R0vY8%211%=3941&YA&UNv0%211&\6%12E<%6231'8&RGr5%B11%D11r4%5321D(F%M3821p0:1p0B1pfFQ11pf0Q21pf<Q61").
Proof.
intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2. right. lia.
Qed.
Lemma reserved_free_hull_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q@'R3'\5yR0%211'J'='D%1244%311&RN&R?r3%211%411&R0vY8%211%=3941'N&YA&Y>&\6%12D;r2%32F1%5231&UOv0%211%:241&UN%114%=21:%?241'8&RGr5%K11%M11r4%5321M(F%Q63821p0:1p0K1pfFQ:1pf0Q;1pf<Q?1").
Proof.
intros model lo n Hres Hlo. rewrite Hres. apply RefNodes.region_free_intro. intros b s Hin.
pose proof (proj1 (Forall_forall _ _) RES_hullH _ Hin) as [H1 H2]. cbn [fst snd] in H1, H2.
pose proof (u64_range s). destruct Hlo; [left | right]; lia.
Qed.
Lemma vis_add_inv : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "RL'U:'X0'='X2%211'J'A%117&W1v0vQ?r5r4r3r2%76654321(5r1%22B1%>3<41'K'Q4'I%A12&X9&V8r7%211%421A%=28<%I3721(TD&V=&VF%118&X5&U5%11;%311&7&VN&U4%11@r6%45Q3A21Q1%63Q:1Q1&VC%11E%@4>:31&U7%11H&U9%11J&TO%11L(9'D%12QHQH(C%14QJQJ@Q@&U8%11Q3%73531&U1%11Q6&Y>&TM%11Q9&W2%11QD%5231&TN%11Q>&U0%11Q@&U6%11QB&U3%11QD&U2%11QF%QB=Q1Q7OMKCA;97531%R=3RBR51%QM2QE1qfNQO1%R12R01p0R31pdDRG1pe@RD1pfFRH1pd4RI1pd>RK1").
Proof.
intros cs b n k cs2 Hv. rewrite vis_add_eq in Hv. unfold vis_add_ref in Hv.
destruct (split_lit b) as [bb bk]. destruct (shadow_of A (kn cs) b n) as [[sb sk] sn] eqn:Hsh.
destruct (xhi (kn cs) n) as [nhi|]; [|discriminate].
match type of Hv with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
injection Hv as <-. exists nhi. split; [reflexivity|]. unfold shadow_facts. rewrite Hsh. reflexivity.
Qed.
Lemma in_allow_ext : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "L'WN'U:'J'='D'X0%2211%411&U8r1%211r2%411%;3631'Q4'8pi221&W;v0r4%33219r3%53431%E3731p0;1pd@H1pd>I1pR<K1").
Proof. intros E cs cs' H. apply functional_extensionality. intros z. unfold in_allow, in_vis, in_sh. rewrite H. reflexivity. Qed.
Definition kind_none (k : mkind) : bool := match k with KNONE | KNONELAZY => true | _ => false end.
Definition kind_lazy (k : mkind) : bool := match k with KRWLAZY | KNONELAZY => true | _ => false end.
Record grant_post (kd : mkind) (a n : word) (model model' : Model) : Prop := GP {
gp_maps : vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model);
gp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
gp_noacc : vm_noaccess (m_vmmaps model') = (if kind_none kd then (a, n) :: vm_noaccess (m_vmmaps model) else vm_noaccess (m_vmmaps model));
gp_lazy : m_vm_lazy model' = (if kind_lazy kd then (a, n) :: m_vm_lazy model else m_vm_lazy model);
gp_mat : m_vm_materialized model' = m_vm_materialized model;
gp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
gp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
gp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
gp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
gp_halted : m_halted model' = m_halted model;
gp_fds : m_fds model' = m_fds model;
gp_fs : m_fs model' = m_fs model;
gp_tid : m_tid model' = m_tid model;
gp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model) }.
Definition grant_mem (kd : mkind) (a n : word) (FULL FULL' : word -> option byte) : Prop :=
(forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
/\ (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n ->
FULL' x = if kind_none kd then None else Some (Z_to_bv 8 0)).
Lemma vis_grant_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R8'V>'\5yR0%211'R3'WN'U:'T3r9r8r7r6r5%6554321'J'='D'X0%2211%411&U8r3%211r4%411%;3631&YCz&\6%12KE%4231'Q4&YEr;%62Q01+TP0%4221%G361:'N%;2Q5Lr=%=2Q71%@231&YA&Y>r<%B2Q<1%3261%5219%;271'8&WEv0r:%3521Q=EQ<%4532Q?:Q=%Q:3621p081p0E1p0F1p0N1p0Q41p0QA1phLQL1pdBQJ1pd>QK1pR<QM1pf>QO1pf<R01pfFR21pcLR31peBR71").
Proof.
intros kd a n model model' E cs cs1 x GPo Hvis Hn Hal Hnl Hx.
unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
rewrite (in_allow_ext E cs cs1 Hvis).
rewrite in_ivs_cons. cbn [fst snd].
assert (T : ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + bv_unsigned n))%bool = false).
{ apply andb_false_iff. destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
rewrite T. cbn [orb].
assert (P : page_in_ranges (page_base x) ((a, n) :: m_vm_lazy model) = page_in_ranges (page_base x) (m_vm_lazy model)).
{ apply page_in_ranges_cons_out; [|exact Hn].
pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal ltac:(rewrite Z.add_mod, Hal, Hnl by lia; reflexivity) Hx).
unfold page_size. lia. }
destruct (kind_none kd); destruct (kind_lazy kd); rewrite ?in_ivs_cons; cbn [fst snd]; rewrite ?T, ?P; cbn [orb]; reflexivity.
Qed.
Lemma grant_wf : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q3'V>'\5yR0%211'R3'T3r5r4r3r2r1%6554321&XF%115&YA&Y>&\6r6%22@1%32A=%5221&YH+2+R0%3221%;251%>1Cp021p0?1p0B1pf>J1pf<K1pfFM1pcLN1peBQ21").
Proof.
intros kd a n model model' GPo (W1 & W2 & W3 & Wsp) Hb. unfold model_ivs_wf.
rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo).
assert (iv_wf (a, n)) by (unfold iv_wf, B, S; cbn; lia).
split; [apply ivs_wf_cons; assumption|].
split; [destruct (kind_none kd); try apply ivs_wf_cons; assumption|].
split; [destruct (kind_lazy kd); try apply ivs_wf_cons; assumption|].
unfold init_sp_ok in *. rewrite (gp_isp _ _ _ _ _ GPo). exact Wsp.
Qed.
Lemma grant_eager_le : forall kd a n model model',
grant_post kd a n model model' -> model_ivs_wf model -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
eager_used model' <= eager_used model + (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n).
Proof.
intros kd a n model model' GPo Hwf Hb.
pose proof (grant_wf kd a n model model' GPo Hwf Hb) as Hwf'.
rewrite (eager_used_sem model' Hwf'), (eager_used_sem model Hwf).
rewrite (gp_maps _ _ _ _ _ GPo).
set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
cbn [sum_count].
assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
<= sum_count (fun x => negb (covered C x)) (vm_maps (m_vmmaps model))).
{ apply sum_count_negb_covered_mono. intros x Hx. subst C C'.
rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app in Hx. rewrite covered_app.
apply orb_true_iff in Hx. apply orb_true_iff.
destruct Hx as [Hx|Hx]; [left|right]; [destruct (kind_none kd) | destruct (kind_lazy kd)]; try exact Hx;
unfold covered in *; cbn [existsb]; rewrite Hx; apply orb_true_r. }
assert (HEAD : iv_count (fun x => negb (covered C' x)) (a, n) <= (if (kind_none kd || kind_lazy kd)%bool then 0 else bv_unsigned n)).
{ destruct (kind_none kd || kind_lazy kd)%bool eqn:Hk.
- unfold iv_count, B, S. cbn [fst snd]. rewrite zcount_false; [lia|]. intros x Hx.
pose proof (u64_range n). rewrite Z2Nat.id in Hx by lia. apply negb_false_iff.
subst C'. rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). rewrite covered_app.
assert (IN : in_iv (a, n) x = true).
{ unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
apply orb_prop in Hk as [Hk|Hk]; rewrite Hk; unfold covered; cbn [existsb]; rewrite IN; cbn [orb];
[reflexivity | apply orb_true_r].
- unfold iv_count, S. cbn [snd]. pose proof (u64_range n).
pose proof (zcount_le_len (fun x => negb (covered C' x)) (B (a, n)) (Z.to_nat (bv_unsigned n))). lia. }
lia.
Qed.
Definition maps_apart (E : env) (ms : list amap) (lo n : Z) : Prop :=
forall m, In m ms -> is_fog m = false ->
lo + n <= bv_unsigned (edenot E (am_base m)) \/
bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= lo.
Lemma maps_apart_of_region_free : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q>'WN'='U?%211'R3'\5yR0%211&W@r5r4&RL&R?r3%211%411%83761'J'8&RG&7'D%12??&RN%<1>%211%?12%73521r2%:32@1(F%>3=21&T7r7r6&\6%12NJ%22OH%645421p081p0H1pfFQ21pcLQ31pf<Q71pf@Q91pR<Q=1").
Proof.
intros E ms model a n Hmaps Hrf m Hin Hnf.
rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf].
exact (RefNodes.region_free_In _ a n (edenot E (am_base m)) (edenot E (am_len m)) Hrf (maps_match_In E ms _ m Hmaps Hin Hnf)).
Qed.
Lemma inside_maps_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QO'WN'\5yR0%211'Ay8%511%311p051'='X2%211'U?%411'X0'Q4&X=vY8r9r8r7%544321&T7r:r3r2%443621'J'8&V0r6r5%35>=<21(F%73621'N&YA&Y>&X;r<(WK%12FE%4231&X:%125>%8231%:21?r4%;2A1%=217%?241p0A1p0J1p0Q01pfFQ71pf0Q81peHQ:1pg6Q:1pd4Q<1pf@Q>1pe@QA1pW2QE1pR<QN1").
Proof.
intros E M k ms b o l lo n HK Hap. induction ms as [|m ms IH]; intros H; [discriminate|].
cbn [inside_maps] in H. apply orb_prop in H as [H|H].
- apply andb_prop in H as [Hnf H]. apply negb_true_iff in Hnf.
pose proof (xinside_sound SEGS E M k b o l (am_base m) 0 (am_len m) HK H) as [I1 I2].
unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *.
destruct (Hap m (or_introl eq_refl) Hnf); lia.
- apply IH; [|exact H]. intros m' Hm'. apply Hap. right. exact Hm'.
Qed.
Definition isp_facts (E : env) : Prop :=
sp_window_lo <= uE E e_sp0 <= sp_window_hi /\ uE E e_sppg = pagedown (uE E e_sp0).
Lemma u_e_top : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "?'WN&T4r1%211'J'Q4&WCr2&UD%3221&WD%114%83731p0:1pR<>1").
Proof.
intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
unfold e_top, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit, u_add64, u_lit64. rewrite Hpg.
unfold two64, sp_window_lo in *. pose proof (u64_range (edenot E e_sp0)).
replace ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) by reflexivity.
replace (pagedown (bv_unsigned (edenot E e_sp0)) + (2 ^ 64 - 8388608))
with ((pagedown (bv_unsigned (edenot E e_sp0)) - 8388608) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
Qed.
Lemma lit_ivs_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'WN'='U?%211'Q4&T7r6r5r4r3%544321&Y:'D%1299(Cr2%24<<71&V<%11<%83631'N&YA&Y>%12A@%321@%32A@%521D%7231p091p0C1pf2J1pcNK1pfFL1pf0M1pf@O1pR<Q31").
Proof.
intros E ms lo n a' m Hap Hin.
destruct (PlaceLemmasK.lit_ivs_In ms a' m Hin) as ((B0 & B1 & B2) & m0 & Hm0 & Hnf & Hb & Hl).
pose proof (Hap m0 Hm0 Hnf) as D. rewrite Hb, Hl in D. cbn [edenot] in D.
unfold two64 in B2. rewrite !u64_lit in D by lia. exact D.
Qed.
Lemma runs_apart_grant : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q='WN'='U?%211'Q4'>&T7r7r6r5r4%544321&YCz%2215&Y:'D%12==%221=(C%14@@;:r3%345A21&XMr8%211%;3841'N&YA&Y>%126G%321G%32HG%5219%7231p091p0F1p0J1pe@Q11pgJQ31pgHQ41pfFQ51pf0Q61pf@Q81pR<Q<1").
Proof.
intros E ms lo n rlo rn k Hap Hn Hin. eapply PlaceLemmasK.runs_apart; [exact Hin | exact Hn |].
intros a' m Hin'. eapply lit_ivs_apart; [exact Hap | exact Hin'].
Qed.
Lemma inside_runs_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R2'WN'\5yR0%211'Ay8%511%311p051'='X2%211'U?%411'X0'Q4&X=vY8r9r8r7%544321&T7r:r3r2%443621&YCz%2215'J'8&V1r6%25;@?>1(F%63521'N&YA&Y>&X;r=(WK%12IH%4231&X:%125J%8231%:21?r5%;2A1%=217%?241p0A1p0I1p0M1p0Q31pfFQ:1pf0Q;1peHQ=1pg6Q=1pd4Q?1pf@QA1pe@QD1pW2QH1pR<R11").
Proof.
intros E M k ms b o l lo n HK Hap Hn H. unfold inside_runs in H.
destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate]. destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate].
pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
apply existsb_exists in H as ([[ra rn] rk] & Hin & Hr). apply andb_prop in Hr as [Hr1 Hr2]. apply Z.leb_le in Hr1. apply Z.leb_le in Hr2.
pose proof (runs_apart_grant E ms lo n ra rn rk Hap Hn Hin) as D.
unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.
Lemma safe_range_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "RK'WN'\5yR0%211'Ay8%511%311p051'='X2%211'U?%411'X0'Q4&X=vY8r9r8r7%544321&T7r:r3r2%443621&YAzr4%3221'N&Y>r5%2215&UOv0%211%;241&UN%114%>218%;241r6%<21;&WDr=%211%E241&T4r>%211&YC%12IQ1'J'8&VKr<r;%36G9=21Q4(F%73621&X;rA(WK%12C8%4231&X:%125:%Q5231%Q;21Q?%Q72Q@QE%Q=216%Q:231p0=1p0F1p0I1p0M1p0Q41p0QA1p0QF1p0QL1pfFR31pf0R41peHR61pg6R61pd4R81pf@R:1pe@R=1pW2RA1pR<RJ1").
Proof.
intros E M k ms b o l lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H. unfold safe_range in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|].
- destruct (xhi k l) as [lh|] eqn:Hlh; [|discriminate]. destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate].
pose proof (xhi_sound SEGS E M k l lh HK Hlh) as L1. pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2].
unfold estart, elenZ. cbn [a_base a_off].
apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H2.
+
pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G. cbn [xt_den] in G.
pose proof (u_e_top E Hsp) as T. unfold uE in T. rewrite T in G. lia.
+ apply Z.leb_le in H1. lia.
- eapply inside_maps_apart; eassumption.
- eapply inside_runs_apart; eassumption.
Qed.
Lemma grant_keep_apart : forall E M k ms K lo n,
know_ok SEGS E M k -> maps_apart E ms lo n ->
0 <= lo -> (lo + n <= img_lo A \/ img_hi A <= lo) -> lo + n <= utop E -> isp_facts E -> 0 < n ->
grant_keep_b A k ms K = true ->
match K with KImg _ _ => False | _ => True end ->
kfoot_apart E K lo n.
Proof.
intros E M k ms K lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H HnI. unfold kfoot_apart, kfoot.
destruct K as [[b o] w v|[b o] l|[b o] l kb|ilo ihi|e m|e rlo rhi|[b o] l|a1 n1 a2 n2|[b o] l fc|[b o] l]; cbn [grant_keep_b] in H;
try exact I; [apply andb_prop in H as [Hw H]; apply Nat.leb_le in Hw| | | destruct HnI | | |];
pose proof (safe_range_apart E M k ms b o _ lo n HK Hap Hlo0 Hlo Hhi Hsp Hn H) as D; try lia.
rewrite elenZ_lit'' in D by lia. lia.
Qed.
Lemma kn_grant_filter_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "RH'WN'\5yR0%211'Ay8%511%311p051phL62'='X2%211'U?%411'Q4&X=vY8r7r6r4%544321&T7r8r3r2%443621&YAz%2219'N&Y>r5%221=&UOv0%211%:241&UN%114%=218%;241%;2G:&WDr;%211%C241&T4r<%211&YC%12GQ1&\6r1%22QD1r:%6221r9%K231%Q0215%N241'Jr>%11Q6r?%11Q8%53QK31p071phLR11r=&V9%13Q4GK%QH4QG831p051p0G1p0J1p0N1p0Q41p0QA1p0QE1p0QK1pfFR21pf0R31pf@R51pe@R81pW4R<1pW2R>1pR<RG1").
Proof.
intros E M M' k ms lo n HK Hap Hlo0 Hlo Hhi Hsp Hn Hout. unfold kn_grant_filter.
pose proof (kimg_clip_in_hull' (List.filter (grant_keep_b A k ms) k)) as Hhull.
unfold know_ok. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) Hhull K Hin) as HKh.
apply kimg_clip_incl in Hin. apply filter_In in Hin as [Hin Hkeep].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
eapply kentry_keep_sem'; [exact HKK | | exact Hout].
destruct K as [| | |ilo ihi| | | | | |];
try (eapply grant_keep_apart; [exact HK | exact Hap | exact Hlo0 | exact Hlo | exact Hhi | exact Hsp | exact Hn | exact Hkeep | exact I]).
unfold kfoot_apart, kfoot. cbn in HKh. lia.
Qed.
Lemma regs_ok_regupd_same : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q?'WN'='X0%211&S?y5'\5yR0%211%5241'>&X>r5r4r3%43321'I&Q0(4%2215uQ0%4271%6231'J&XN&\4&YG%11>%32G1%52A1%73F1@r8r7&Y0r6%91G%;2O1%4331H%K3761p091p0B1p0J1phDQ21pfFQ11pW:Q31ph4Q:1pR<Q>1").
Proof.
intros E sr R n v HR Hn Hv r.
assert (Hne : Z_to_bv 5 (Z.of_nat n) <> 0%bv).
{ intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Z_to_bv_unsigned in Hz. unfold bv_wrap in Hz.
change (bv_modulus 5) with 32%Z in Hz. rewrite Z.mod_small in Hz by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z in Hz by reflexivity. lia. }
destruct (bv_eqb r (Z_to_bv 5 (Z.of_nat n))) eqn:Hr.
- apply (proj1 (bv_eqb_eq _ _)) in Hr. subst r. rewrite getr_same by exact Hne. rewrite <- Hv. apply HR.
- assert (Hr' : r <> Z_to_bv 5 (Z.of_nat n)) by (intros ->; rewrite bv_eqb_refl in Hr; discriminate).
rewrite getr_other by exact Hr'. apply HR.
Qed.
Lemma grant_new_facts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "SN'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r8r7r6r5r4%<;;:987654321'J'8&RG&7'D%12KK&RN&R?%11;%311&RL%113%93731r3%<32@1(F%@3?21&\6%12Q9D%C3Q116&YCz%221H'N&YA&Y>%92QAO%221N&UO%11Q8%6231&UN%11Q;%9217%;241%B2QJQ9%;21Q8&WDr=%211%@241'Ir:%J2R21r1%L2R41%F231%F24QE%L231%8231&W=r2%Q32R;1r<%Q?11%Q=11%6241(:%QJ3QI21&RM%116%;291%QN3QM15r@%R821=%R13R018&W<%12R>?%R43R31;&YB%Q117%221C%R83R71?&WEr?%25RF<1FH%R<3R;1C%Q4251%Q52:1%Q62>1%Q72B1%Q82G1p0Q11phLS91p0Q<1p0QC1p0R01p0R41p0R81p0RJ1pfHS81pfFSA1pcLSB1pf<S<1pRHS>1pW:SD1pd>SK1pR<SM1").
Proof.
intros E cs R FULL model a n nZ HC Hrf Un HnZ Himg HaC x Hx.
rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
pose proof (region_free_sem _ a n (bv_unsigned x) Hrf2 ltac:(rewrite Un; lia) ltac:(rewrite Un; lia)) as M0.
assert (N0 : in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false).
{ destruct (in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model))) eqn:En; [|reflexivity]. exfalso.
apply (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC) in En. congruence. }
assert (Hh : in_hull A (bv_unsigned x) = false).
{ unfold in_hull. apply andb_false_iff. destruct Himg; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia. }
assert (Hc : (utop E <=? bv_unsigned x) = false) by (apply Z.leb_gt; lia).
repeat split; try assumption.
- destruct (argH E x) eqn:Ea; [|reflexivity]. pose proof (argH_high _ _ Ea). pose proof (utop_bounds E). lia.
- unfold vis. rewrite Hh, Hc, M0. reflexivity.
Qed.
Lemma grant_cs1_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "W@'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'V>'Q4'='X0%211'X2%411'8'>'W9vY8v0vQ?vY9vZ0vQ:rDrCrBrAr@%<;;:987654321'J&\6r>%22Q21r=%53J21&YCz%2216&YEr?+TP0%3221%=3Q216%=2Q=B%6214%@3Q519'N&YA&Y>%C2QCI%221H&UO%11Q2%6231&UN%11Q5%9217%;241%L2QLQ3%;21Q2&WDrJ%211%@241&RG&7'D%12R4R4&RN&R?rG%211%411&RL%113%:3831rE%=321QF(F%QB3R121'T3rFrH%35=271QK&T2%153?4HQM&X>rN%231R0QO&WMrO%221R1rI%R03RN21rQ0%621R5%R33S114&X=rQ1&W6%16RBR?26BN%44RD31R>&B&T6rM%211&T5%113%6231&?%11RD%RB3S131&V5%11J(:%RF3S521rL%R621RN%RI3S8ROQ8&TOrQ5%211&TM%113%R<231%R=21Q<%R?21S;p091&U9%119%RC2S;1'U?&Y:r1&U4rQ7%211%53641&V4r2%211%S@3SO1QOrQ4%SA2TA1rQ2%S1221&WCrQ:&U<r3%211%5241%S9271&U>%115%9281%S<251%S>21>%S@261p0B1p0G1pf2N1&U;rK&V9&V8%11O%33TE1O%S73TL51(TErQ3%23S>R?1%:8Q5R44S01RJS6RK'IrQ9%TO;TNTMTLTKTJTI1Q:R7RERA%TB2UBQ;%T>21Q2%T32Q12%T5221rQ;%RB7U3U01Q0Q5RCQ:rQ8%RD7U5U23Q4Q@1Q<%TK3UD31p061phLUK1%RH6U9U6=QFRMS1%RI6U:U7>6RNS2%U03UH21%A241%B2@1tdBV6D1p0Q01p0R01p0R41p0R?1p0RB1p0RG1p0S21p0S81p0S<1p0SB1p0SF1p0SI1p0SN1p0T?1p0TF1p0U31p0U71p0U=1p0UA1p0UH1pg2V61pi0V>1pdJV91pfNV@1pfLV?1pd:V@1peFV>1pW<VL1ph6VB1pRJVI1pf>VI1pfHVH1pfFW21pcLW31peBVL1pf<VN1pRHW01pW:W61pd>W=1pR<W?1").
Proof.
intros E cs R FULL model kd a n nZ model' FULL' sr' R' knew be ne nhi eager ylo' nx'
HC Un HnZpos HnZal Hal Himg_a HaC Hrf GPo [GM1 GM2] Hregs Hbase HneE Hknew Hkind Hkfog Hnhi Hbudget Hylo Hholes cs1.
pose proof (u64_range a) as Ra. pose proof (utop_bounds E) as UB.
pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP1 ISP2]. pose proof ISP2 as ISP. unfold sp_window_lo, sp_window_hi in ISP2.
pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as Hmaps.
pose proof (maps_apart_of_region_free E (a_maps cs) model a n Hmaps Hrf) as Hapart. rewrite Un in Hapart.
pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
pose proof (grant_new_facts E cs R FULL model a n nZ HC Hrf Un HnZpos Himg_a HaC) as NEW.
assert (VISOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
VIS E cs1 model' x = VIS E cs model x).
{ intros x Hx. eapply vis_grant_out; [exact GPo | reflexivity | rewrite Un; lia | exact Hal | rewrite Un; exact HnZal | rewrite Un; exact Hx]. }
assert (HIDOUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
HID E cs1 model' x = HID E cs model x).
{ intros x Hx. unfold hid. rewrite (VISOUT x Hx). reflexivity. }
assert (MROUT : forall x : word, bv_unsigned x < bv_unsigned a \/ bv_unsigned a + nZ <= bv_unsigned x ->
MR E cs1 model' FULL' x = MR E cs model FULL x).
{ intros x Hx. unfold Mr, mrestrict. rewrite (HIDOUT x Hx). rewrite (GM1 x) by (rewrite Un; exact Hx). reflexivity. }
assert (MRSAME : MR E cs1 model' FULL' = MR E cs model' FULL').
{ unfold Mr. rewrite (hid_ext A argH E cs cs1 model') by reflexivity. reflexivity. }
split; [| split; [exact MROUT | exact MRSAME]].
pose proof (grant_wf kd a n model model' GPo Hwf ltac:(rewrite Un; lia)) as Hwf'.
destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
constructor.
all: unfold cs1, add_entry; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss].
all: try change (ALLOW E (ACS ?s ?m ?t ?y ?e (a_vis cs) (a_ghost cs) ?ab ?br ?fd ?ti ?hn ?hl)) with (ALLOW E cs).
- exact Hregs.
- reflexivity.
- apply Forall_app. split.
+ unfold cs1, add_entry in MRSAME. cbn [kn a_ss s_know mk_ss] in MRSAME. rewrite MRSAME. exact Hknew.
+ eapply kn_grant_filter_ok; [exact Xknow | exact Hapart | lia | exact Himg_a | exact HaC | exact ISP | exact HnZpos | exact MROUT].
- rewrite (gp_halted _ _ _ _ _ GPo). exact Xhalt.
- unfold fds_ok in *. rewrite (gp_fds _ _ _ _ _ GPo), (gp_fs _ _ _ _ _ GPo). exact Xfds.
- rewrite (gp_fs _ _ _ _ _ GPo). exact Xfs.
- rewrite (gp_tid _ _ _ _ _ GPo). exact Xtid.
- rewrite (gp_res _ _ _ _ _ GPo). exact Xres.
- rewrite (gp_limit _ _ _ _ _ GPo). exact Xlimit.
- rewrite (gp_maps _ _ _ _ _ GPo). rewrite <- Hbase, <- HneE. apply maps_match_cons; [exact Hkfog | exact Xmaps].
-
rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo). apply Forall_cons.
+ intros Hh. exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. destruct kd; cbn in Hkfog, Hh; discriminate.
+ apply Forall_forall. intros m Hm Hk. destruct (proj1 (Forall_forall _ _) Xholes m Hm Hk) as [F1 F2]. split; [|lia].
intros iv Hiv. apply in_app_iff in Hiv as [Hiv|[<-|Hiv]].
* apply F1. apply in_app_iff. left. exact Hiv.
* cbn [fst snd]. rewrite Un. pose proof (Hholes m Hm Hk). lia.
* apply F1. apply in_app_iff. right. exact Hiv.
- rewrite (gp_maps _ _ _ _ _ GPo). constructor; [|exact Xseps].
apply Forall_forall. intros [b s] Hin. unfold iv_disjoint. cbn [fst snd]. rewrite Un.
rewrite region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf2].
pose proof (RefNodes.region_free_In _ a n b s Hrf2 Hin). rewrite Un in *. lia.
- exact Hwf'.
- rewrite (gp_maps _ _ _ _ _ GPo). apply Forall_cons; [|exact Xbounds]. cbn [fst snd]. rewrite Un. repeat split; lia.
- rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [apply Forall_cons; [cbn [fst snd]; rewrite Un; lia|]|]; exact Xlazyb.
- intros z Hz. rewrite (gp_maps _ _ _ _ _ GPo). rewrite in_ivs_cons. rewrite (gp_noacc _ _ _ _ _ GPo) in Hz.
destruct (kind_none kd); [rewrite in_ivs_cons in Hz; apply orb_prop in Hz as [Hz|Hz]; [rewrite Hz; reflexivity|]|];
rewrite (Xnasub z Hz); apply orb_true_r.
- apply Forall_cons.
+ cbn [am_kind amap_den am_base am_len]. intros Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
replace (kind_none kd) with true by (destruct Hk as [-> | ->]; reflexivity). left. unfold amap_den. cbn [am_base am_len]. rewrite Hbase, HneE. reflexivity.
+ apply Forall_forall. intros m Hm Hk. rewrite (gp_noacc _ _ _ _ _ GPo).
pose proof (proj1 (Forall_forall _ _) Xnone m Hm Hk) as X. destruct (kind_none kd); [right|]; exact X.
- apply Forall_cons.
+ cbn [am_kind am_base am_len]. intros Hk x Hx. subst kd. rewrite Hbase, HneE, Un in Hx. cbn in Hkind.
rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). cbn [kind_none kind_lazy]. split.
* exact (proj1 (proj2 (NEW x Hx))).
* destruct (page_of_byte_in_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) Hx) as [P1 P2].
apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
+ apply Forall_forall. intros m Hm Hk x Hx.
destruct (proj1 (Forall_forall _ _) Xkinds m Hm Hk x Hx) as [K1 K2].
rewrite (gp_noacc _ _ _ _ _ GPo), (gp_lazy _ _ _ _ _ GPo). split.
* destruct (kind_none kd); [|exact K1]. rewrite in_ivs_cons. cbn [fst snd]. rewrite K1, Un.
pose proof (Hapart m Hm ltac:(unfold is_fog; rewrite Hk; reflexivity)) as D.
replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ))%bool with false; [reflexivity|].
symmetry. apply andb_false_iff. destruct D; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
* destruct (kind_lazy kd); [|exact K2]. rewrite page_in_ranges_cons, K2. apply orb_true_r.
- rewrite (gp_res _ _ _ _ _ GPo), (gp_maps _ _ _ _ _ GPo).
rewrite sum_sizes_app in *. cbn [sum_sizes snd]. rewrite Un. cbn [sum_sizes] in Xtotsz. lia.
- rewrite (gp_isp _ _ _ _ _ GPo). exact (conj ISP1 ISP2).
- rewrite (gp_brk _ _ _ _ _ GPo). exact Xbrk.
- rewrite (gp_brk _ _ _ _ _ GPo), (gp_sbrk _ _ _ _ _ GPo). exact Xsbrk.
- pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. lia.
- exact Xabytes.
- destruct Xminv as [N1 N2 N3 N4 N5]. constructor; rewrite ?(gp_mat _ _ _ _ _ GPo), ?(gp_limit _ _ _ _ _ GPo); try assumption.
+ intros p Hp. rewrite (gp_lazy _ _ _ _ _ GPo). destruct (kind_lazy kd); [rewrite page_in_ranges_cons, (N4 p Hp); apply orb_true_r | exact (N4 p Hp)].
+ pose proof (grant_eager_le kd a n model model' GPo Xwf ltac:(rewrite Un; lia)) as EG. rewrite Hkind in EG.
destruct eager; cbn [negb] in EG; [|lia]. rewrite Un in EG. rewrite Xlimit. specialize (Hbudget eq_refl). lia.
- intros x Hh Hm Hna Hlz Hgh.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + nZ)) as [Hlt2|Hge2]].
+ rewrite (GM1 x) by lia. apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
* rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
apply andb_prop in Hm as [Hm _]. apply Z.leb_le in Hm. cbn [fst] in Hm. lia.
* rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
* rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
+ rewrite (GM2 x) by (rewrite Un; lia).
rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [|reflexivity].
rewrite in_ivs_cons in Hna. cbn [fst snd] in Hna. apply orb_false_iff in Hna as [Hna _].
apply andb_false_iff in Hna as [Hna|Hna]; [apply Z.leb_gt in Hna | apply Z.ltb_ge in Hna; rewrite Un in Hna]; lia.
+ rewrite (GM1 x) by (rewrite Un; lia). apply Xzero; [rewrite <- (HIDOUT x) by lia; exact Hh | | | | exact Hgh].
* rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons in Hm. apply orb_prop in Hm as [Hm|Hm]; [|exact Hm].
apply andb_prop in Hm as [_ Hm]. apply Z.ltb_lt in Hm. cbn [fst snd] in Hm. rewrite Un in Hm. lia.
* rewrite (gp_noacc _ _ _ _ _ GPo) in Hna. destruct (kind_none kd); [rewrite in_ivs_cons in Hna; apply orb_false_iff in Hna as [_ Hna]|]; exact Hna.
* rewrite (gp_lazy _ _ _ _ _ GPo) in Hlz. destruct (kind_lazy kd); [|exact Hlz].
rewrite page_in_ranges_cons_out in Hlz; [exact Hlz | | rewrite Un; lia].
pose proof (page_of_byte_out_aligned x (bv_unsigned a) (bv_unsigned a + nZ) Hal ltac:(rewrite Z.add_mod, Hal, HnZal by lia; reflexivity) ltac:(lia)). unfold page_size. rewrite Un. lia.
- eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply GM1. pose proof (argH_high _ _ Hx). rewrite Un. lia.
- rewrite (gp_noacc _ _ _ _ _ GPo), Xhna. unfold RNA. cbn [am_kind am_base am_len].
destruct kd; cbn [kind_noneb kind_none hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
- rewrite (gp_lazy _ _ _ _ _ GPo), Xhlz. unfold RLZ. cbn [am_kind am_base am_len].
destruct kd; cbn [kind_lazyb kind_lazy hreplay]; rewrite ?Hbase, ?HneE; reflexivity.
- intros Ht. rewrite (gp_tid _ _ _ _ _ GPo). exact (Xtidv Ht).
Qed.
Definition null_base (cs : acs) : expr := escale 4096 (EVar (nxt cs)).
Definition null_vlo (cs : acs) (nlo : Z) : Z := grant_vlo A (a_maps cs) nlo.
Definition null_vhi (nlo : Z) : Z := (TOPC - nlo) / 4096.
Definition null_kv (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo ++ kn cs.
Definition null_kd (cs : acs) (ne : expr) : list kentry :=
kdisj_fixed A (kn cs) (null_base cs) ne ++ kdisj_new (a_maps cs) (null_base cs) ne.
Definition null_kfacts (cs : acs) (ne : expr) (nlo : Z) : list kentry :=
KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo) :: null_kend (null_base cs) ne nlo
++ null_kd cs ne ++ flat_map (kdisj_shadow_twin A (null_kv cs ne nlo)) (null_kd cs ne).
Definition null_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nlo nhi : Z) : acs :=
add_entry cs (sr_upd (s_regs (a_ss cs)) 10 (null_base cs))
(null_kfacts cs ne nlo ++ kn_grant_filter A (kn cs) (a_maps cs))
(Datatypes.S (nxt cs)) (AM (null_base cs) ne kd) nhi eager (a_ylo cs).
Lemma mmap_null_eq : forall (split : bool) cs kd (eager visible : bool),
mmap_null A nx0 LIMIT split cs kd eager visible =
match mmap_len cs with
| Some (ne, nlo, nhi) =>
if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) ne
&& gap_ok A cs nhi && (negb eager || budget_ok LIMIT cs nhi)
&& no_holes (a_maps cs))%bool then
let v := nxt cs in
let cs1 := null_cs1 cs kd eager ne nlo nhi in
let fin (c : acs) := if visible then vis_add A LIMIT c (null_base cs) ne ([KWr (SA (null_base cs) 0) ne; KZero (SA (null_base cs) 0) ne] ++ kn c) else Some c in
let single := match fin cs1 with Some c => Some (contra_cs c, c) | None => None end in
if negb (split && visible) then single else
match first_run (a_maps cs) with
| Some (lo, hi) =>
let vtopL := (lo - nlo) / 4096 in
let vbotH := zcdiv' hi 4096 in
if (Z.leb vbotH (null_vlo cs nlo) || Z.ltb vtopL (null_vlo cs nlo))%bool then single
else if Z.ltb (null_vhi nlo) vbotH then
match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)) with
| Some c => Some (contra_cs c, c) | None => None end
else
match fin (set_kn cs1 (KRange (EVar v) (null_vlo cs nlo) vtopL :: kn cs1)),
fin (set_kn cs1 (KRange (EVar v) vbotH (null_vhi nlo) :: kn cs1)) with
| Some cL, Some cH => Some (cL, cH)
| _, _ => None
end
| None => single
end
else None
| None => None
end.
Proof. intros. reflexivity. Qed.
Hypothesis HULL_lt : hull_lt A.
Lemma null_kend_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QH'WN'\5yR0%211'Ay8%511%311p051'X0'Q4'J&WMr7r5%3221r2%63>21r8%7215%93A14&YA+TP0&\6r4%22G1%5241r6%7213&Y>%72L3%82MA%3221&TL%=221&X=vY8r<r;&VBr:r9%3321H%847651p0:1p0A1p0D1p0K1p0O1pfFQ>1pcLQ?1pg0Q91pfLQ;1pd8Q<1pW2Q>1pR<QG1").
Proof.
intros E M base ne nlo a n Hb Hn Hlo Hnlo HaC. unfold null_kend.
pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn. unfold two64 in *.
destruct ne; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil;
cbn [kentry_ok]; unfold eadd; rewrite AX2SK.mkAlu_denot; cbn [alu64 alu]; rewrite bv_add_unsigned, Hb, Hn;
unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64)%Z;
unfold TOPC in *; rewrite Z.mod_small by lia; lia.
Qed.
Lemma null_kend_pure : forall base ne nlo,
Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kend base ne nlo).
Proof. intros. unfold null_kend. destruct ne; repeat constructor. Qed.
Lemma escale_4096_denot : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'WN'>'\5yR0%211'J&WOr3r2%3221&\4&Y?&\6r1%22;1+TP0%5221%72>1%=3>91'Q4&YE%92B=%2217z%C3521&WMr5&UE(WGr4%211%42@1%7261%L3M1Jp0:1p0A1pcLQ01phDQ41pR<Q61").
Proof.
intros E v a Hv Hal. unfold escale. rewrite mkMd_denot. cbn [edenot]. rewrite Hv.
pose proof (u64_range a) as Ra. apply bv_eq. rewrite u_mul64.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite !u64_lit by lia. rewrite Z.mod_small by lia. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma grant_hull_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QL'R3'\5yR0%211'Q4'J'='D%1255%311&RN&R?r4%211%411&R0vY8%211%=3941'8&RG&7r5%<11%>11&RL%113%63C31r3%932A1(F%J3<21&\6%12OE%M3N16&YCz%221I'N&YA&Y>r7%:2Q81%321E&UOv0%211%8241&UN%114%;218%=241p0?1p0C1p0G1p0Q51pfHQD1pfFQF1pcLQG1pf<QK1").
Proof.
intros model a n nZ Hres Hrf Un HnZ. pose proof HULL_lt as HL. unfold hull_lt in HL.
rewrite region_free_app in Hrf. apply andb_prop in Hrf as [Hrf1 _]. rewrite Hres in Hrf1.
destruct (Z_lt_le_dec (bv_unsigned a) (img_hi A)) as [H1|H1]; [|right; lia].
destruct (Z_lt_le_dec (img_lo A) (bv_unsigned a + nZ)) as [H2|H2]; [|left; lia].
exfalso. set (z := Z.max (bv_unsigned a) (img_lo A)).
pose proof (HULL_tiled z ltac:(unfold z; lia)) as T.
rewrite (region_free_sem _ a n z Hrf1 ltac:(lia) ltac:(unfold z; lia)) in T. discriminate T.
Qed.
Lemma alloc_top_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q?'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321'J'Q4&R5&R?%117%311&YI&WCr6&UB%3221+XPPP0%6221%=3<81p0?1pf<M1pRHO1pW:Q51pd>Q<1pR<Q>1").
Proof.
intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [ISP _].
unfold alloc_top, stack_max_size. rewrite ISP. reflexivity.
Qed.
Lemma alloc_top_utop : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QA'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321'I&YA&WDr6%211&R5&R?%11:%311%8251&YC&Y>+TP0%2291%4261%?261p0A1pf<O1pRHQ11pW:Q71pd>Q>1pR<Q@1").
Proof.
intros E cs R FULL model HC. rewrite (alloc_top_eq E cs R FULL model HC). apply utop_bounds.
Qed.
Lemma le_utop : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QE'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r6r5r4r3r2%<;;:987654321'J&YE+TP0%2251z%53C21&YA&R5&R?%11=%311%52>1&WDr9%211%92C1p051p0<1p0C1pi2Q11pf<Q31pRHQ51pW:Q;1pd>QB1pR<QD1").
Proof.
intros E cs R FULL model z HC Hz Hle. rewrite (alloc_top_eq E cs R FULL model HC) in Hle.
exact (le_utop_of_aligned E z Hz Hle).
Qed.
Lemma utop_le_TOPC : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321&YA&WDr6%211&TL%5221p071pf<E1pRHG1pW:M1pd>Q41pR<Q61").
Proof.
intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]]. pose proof (utop_bounds E).
unfold TOPC, sp_window_hi in *. lia.
Qed.
Lemma isp_facts_of : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321&T4r6%211p041pf<B1pRHD1pW:J1pd>Q11pR<Q31").
Proof. intros E cs R FULL model HC. exact (proj2 (co_isp _ _ _ _ _ _ _ _ _ _ _ HC)). Qed.
Lemma grant_ok_na_pin_parts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QE'R3'\5yR0%211'Q4'J'8&XIr3r2r1%43321(F%83721'I&YE&\6%12?9+TP0%4221z%@3A21&YC%1236&YA&Y>%129A&R5&R?r4%211%411%8261&RG&7'D%12Q1Q1&RN%118&RL%11:%73531&\4%12Q9Q2%;33Q41%Q83Q71Q1%Q02>1%Q12H1%Q22K1p0Q41pfHQ>1pcLQ@1pf<QD1").
Proof.
intros model a nZ Hg. unfold grant_ok_na_pin in Hg.
apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal.
repeat split; assumption.
Qed.
Lemma null_grant_facts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "S9'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r7r6r5r4r3%<;;:987654321'J'8&XIr2%23761(F%63521&YCz%221;&YE+TP0%22?1%=3K15'I&\6%12Q7E%7216%B3Q01:&YA%1294&Y>%126J&WDr;%211%7241&TL%9231&\4%12QEQ2%@2QF1%Q03Q>1Q4&RG&7'D%12QJQJ&RN&R?%11Q=%311&RL%113%93731%;31QA>%Q=3Q<1Q8'N&UO%11QK%N2K1&UN%11QN%Q121Q4%7241&T7&U4r:%211%44Q21Q:QN%Q=261%Q>2?1%Q?2M1%Q@2Q21%QA2Q51%QB2Q<1%QC2Q?1p0QE1p0QJ1p0QN1p0R61pfHRD1pcLRM1pf<RG1pRHRI1pW:RO1pd>S61pR<S81").
Proof.
intros E cs R FULL model a nZ HC Hg HnZ HnZal.
destruct (grant_ok_na_pin_parts model a nZ Hg) as (Hal & Hpos & Htop0 & Hrf).
assert (Htop : bv_unsigned a + nZ <= utop E).
{ eapply le_utop; [exact HC | rewrite Z.add_mod, Hal, HnZal by lia; reflexivity | exact Htop0]. }
pose proof (utop_le_TOPC E cs R FULL model HC) as HT.
pose proof (u64_range a) as Ra.
assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; unfold TOPC in *; lia).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (H4096 : 4096 <= bv_unsigned a) by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
pose proof (grant_hull_apart model a (Z_to_bv 64 nZ) nZ (co_res _ _ _ _ _ _ _ _ _ _ _ HC) Hrf Un HnZ) as Hhull.
pose proof (maps_apart_of_region_free E (a_maps cs) model a (Z_to_bv 64 nZ) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hrf) as Hap.
rewrite Un in Hap.
repeat split; assumption.
Qed.
Lemma u_e_stk_len : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "E'WN&T4r1%211'J'Q4&WCr2&UC%3221&YI&YH+2+Q?%3221&WD%119%7231%>3=91p0@1pR<D1").
Proof.
intros E [Hsp Hpg]. pose proof (utop_bounds E) as UB. unfold utop in UB |- *.
unfold e_stk_len, esub, uE in *. rewrite mkAlu_denot, edenot_lit.
rewrite u_sub64, u_lit64, Hpg. unfold two64, sp_window_lo, sp_window_hi in *.
rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia. rewrite Z.mod_small; lia.
Qed.
Lemma kdisj_new_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QG'WN'\5yR0%211'Ay8%511%311p051'='U?%211'X0'Q4'J&\6&WMr7r4%3221%52B1r2%83921r8%8216%:2G1%<3=15&T7r9r3%342=<1&YCz%221?'Q1'X2&X<vY8r;r:%43321&V6%13>CI%93831p0;1p0?1p0D1p0I1pfFQ31pf0Q41pfLQ61pfJQ71pf@Q91pW2Q=1pR<QF1").
Proof.
intros E M ms nb ne lo n Hb Hn Hap HnZ. pose proof (u64_range (edenot E nb)) as Rb. rewrite Hb in Rb.
unfold kdisj_new. apply Forall_app. split.
- unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
pose proof (runs_apart_grant E ms lo n rlo rn k Hap HnZ Hin) as D.
pose proof (PlaceLemmasK.runs_bounds ms rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hb, Hn.
rewrite !u64_lit by lia. lia.
- unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
pose proof (Hap m Hm Hfm) as D.
cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hb, Hn. lia.
Qed.
Lemma kdisj_new_pure : forall ms nb ne,
Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new ms nb ne).
Proof.
intros ms nb ne. unfold kdisj_new, kdisj_merged, kdisj_new1. apply Forall_app. split.
- apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
- apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.
Lemma null_kfacts_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "SI'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'X0'Q4'W9vY8v0vQ?vY9vZ0vQ:r<r;r:r9r8%<;;:987654321'J'D%12A@%221A%I11&V?%11<(5(Cr7%24IH<1r6%44:J21%62:1%>3:81&WOr>&VCr=%211%5241&\4&Y?&\6%12Q@=+TP0%4221%62QC1%L3QC81&WMr?%221Q3%Q03QG1E%:2QIH%Q23Q@1G&YA%12Q9K&YCz%221Q9&YE%12Q<@%Q:3QH14'8&XIr@%231QDQB(F%Q@3521'I&X=rE&T:rD%2319H%54R34QK1&T8%114%M271%QK3RB1Q9&T<%128O%Q72RFQ<%Q921Q6%M231&T;%11Q4%Q0241%C241%D2:1%E2?1p0G1p0N1p0Q21p0Q61p0Q91p0Q<1p0QA1p0R01p0R@1pW4S11pfHRO1pfFS91pcLS:1pfNS21pg0S31pfLS51pf<S71pRHS91pW:S?1pd>SF1pR<SH1").
Proof.
intros E cs R FULL model ne nlo nhi a n nZ M' HC HML Hv Hne Un Hnlo HnZ HnZal Hg. pose proof HULL_lt as HL. unfold hull_lt in HL.
destruct (null_grant_facts E cs R FULL model a nZ HC Hg HnZ HnZal) as (Hal & H4096 & Htop & HT & Un' & Hrf & Hhull & Hap).
pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ ISP]. pose proof (utop_bounds E) as UB.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK0.
pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
assert (Hbase : edenot E (null_base cs) = a) by (unfold null_base; apply escale_4096_denot; assumption).
assert (VLH : null_vlo cs nlo <= bv_unsigned a / 4096 <= null_vhi nlo).
{ unfold null_vlo, null_vhi. split.
- eapply (PlaceLemmasK.grant_vlo_sound A (a_maps cs) (bv_unsigned a) nZ nlo HnZ Hnlo H4096 Hal Hhull HU2).
intros lo n0 k Hin. eapply runs_apart_grant; [exact Hap | exact HnZ | exact Hin].
- apply Z.div_le_mono; lia. }
split; [|exact (conj Hbase VLH)].
assert (KR : forall M, kentry_ok SEGS E M (KRange (EVar (nxt cs)) (null_vlo cs nlo) (null_vhi nlo))).
{ intros M. cbn [kentry_ok edenot]. rewrite Hv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite u64_lit by lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
exact VLH. }
assert (KE : forall M, know_ok SEGS E M (null_kend (null_base cs) ne nlo)).
{ intros M. eapply null_kend_ok; [exact Hbase | exact Hne | exact H4096 | lia | lia]. }
assert (KD : forall M, Forall (kentry_ok SEGS E M) (null_kd cs ne)).
{ intros M. unfold null_kd. apply Forall_app. split.
-
pose proof (u_e_top E ISP) as T. pose proof (u_e_stk_len E ISP) as L. unfold uE in T, L.
unfold kdisj_fixed. apply Forall_app. split; [|apply Forall_app; split].
+ constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off].
* rewrite !edenot_lit, !u64_lit by (unfold KHI in *; lia). rewrite Hbase, Hne, Un. lia.
* rewrite Hbase, Hne, Un. right. unfold uE in UB. lia.
+ apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _.
destruct (lin_ge0 (kn cs) [(b, off)] [(e_top, 0%Z)]) eqn:G; [|constructor]. constructor; [|constructor].
pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK0 G) as G'. cbn [xt_den] in G'. rewrite T in G'.
cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. right. lia.
+ constructor; [|constructor]. cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]. rewrite T, L, Hbase, Hne, Un.
right. lia.
-
unfold kdisj_new. apply Forall_app. split.
+ unfold kdisj_merged. apply Forall_flat_map. apply Forall_forall. intros [[rlo rn] k] Hin.
destruct (Nat.leb 2 k); [|constructor]. constructor; [|constructor].
pose proof (runs_apart_grant E (a_maps cs) (bv_unsigned a) nZ rlo rn k Hap HnZ Hin) as D.
pose proof (PlaceLemmasK.runs_bounds (a_maps cs) rlo rn k Hin) as (B0 & B1 & B2). unfold two64 in B2.
cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite !edenot_lit, Hbase, Hne, Un.
rewrite !u64_lit by lia. lia.
+ unfold kdisj_new1. apply Forall_flat_map. apply Forall_forall. intros m Hm.
destruct (is_fog m) eqn:Hfm; [constructor|]. constructor; [|constructor].
pose proof (Hap m Hm Hfm) as D.
cbn [kentry_ok]. unfold estart, elenZ; cbn [a_base a_off]. rewrite Hbase, Hne, Un. lia. }
unfold null_kfacts. apply Forall_cons; [exact (KR M')|]. apply Forall_app. split; [exact (KE M')|].
apply Forall_app. split; [exact (KD M')|].
apply (kdisj_shadow_twins_ok SEGS A SHADOW_ok' E (MR E cs model FULL)); [|exact (KD _)].
unfold null_kv. apply Forall_cons; [exact (KR _)|]. apply Forall_app. split; [exact (KE _)|].
exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
Qed.
Lemma kdisj_shadow_twin_pure : forall k K,
Forall (fun K' => match K' with KImg _ _ => False | _ => True end) (kdisj_shadow_twin A k K).
Proof.
intros k K. unfold kdisj_shadow_twin.
destruct K as [| | | | | | |[b1 o1z] n1 [b2 o2z] n2| |]; try constructor.
destruct o1z; try constructor. destruct o2z; try constructor.
destruct (split_lit b1) as [c1 o1]. destruct (split_lit b2) as [c2 o2].
destruct (shadow_of A k b1 n1) as [[sb1 sk1] sn1]. destruct (shadow_of A k b2 n2) as [[sb2 sk2] sn2].
match goal with |- Forall _ (if ?c then _ else _) => destruct c; [|constructor] end.
constructor; [exact I | constructor].
Qed.
Lemma null_kd_pure : forall cs ne,
Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kd cs ne).
Proof.
intros cs ne. unfold null_kd, kdisj_fixed, kdisj_new, kdisj_merged, kdisj_new1.
apply Forall_app. split; [|apply Forall_app; split].
- apply Forall_app. split; [repeat constructor|]. apply Forall_app. split; [|repeat constructor].
apply Forall_flat_map. apply Forall_forall. intros [[b off] len] _. destruct (lin_ge0 _ _ _); repeat constructor.
- apply Forall_flat_map. apply Forall_forall. intros [[lo n] k] _. destruct (Nat.leb 2 k); repeat constructor.
- apply Forall_flat_map. apply Forall_forall. intros m _. destruct (is_fog m); repeat constructor.
Qed.
Lemma null_kfacts_pure : forall cs ne nlo,
Forall (fun K => match K with KImg _ _ => False | _ => True end) (null_kfacts cs ne nlo).
Proof.
intros cs ne nlo. unfold null_kfacts. apply Forall_cons; [exact I|]. apply Forall_app. split; [apply null_kend_pure|].
apply Forall_app. split; [apply null_kd_pure|].
apply Forall_flat_map. apply Forall_forall. intros K _. apply kdisj_shadow_twin_pure.
Qed.
Lemma mmap_null_cs1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "X>'U:'V>'8'X0'Q4'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r7r=r6r5r4%<;;:987654321'J'D%12NM%221N%G11&V?r>%211(5(Cr;r:%34Q8Q721r9%54<Q921%72<1%@3<91&ULv[Ar?%3221(F%F3QC21&UF&VCr@%211%421Q0%L3QI17%M3QJ:8&YA&Y>&TOrB%211&TM%113%6231%721Q;%921QAp0;1&B&T6rA%211&T5%113%6231&?%11H%QB3R?31&V5%11C(:%QF3RC21&VA&U4rD%211%411%QL3RI1Q7&\6&WM&VHrEu;%3221%52Q@1%72RJ1&REr1%211&\4%12RO3&XIr2%23QIR61%R=3S:1QH'T3rH%251QM5QGR:&T2rIr3%352QK1QCR>'>rK%QO11&W:rF&Y?%N2SAQJ+TP0%3221%F2SD1%736I1&T9rMrLrJ%4632>1BE'I&Y0rG&YGu:%211%Q32T31%6351QCrC%SK;SJSISHSGSFSEQ3Q82R=1&T8rN%211%QD2Q71%SC3T81QJ%QF2Q9N%SE3T:1SK%QI2T<SLr8%SH3TC21&X?%13S8Q;Q?%S31;%331Q=QA&WO%12QCQ;%R22TER6%Q621Q4%QI2TG1%T23TG41&YE%125Q8z%T63U121%S92Q;8%S929A&WD%11QO%S=231&TL%S?231%S@2Q;G%SA2HQM%Q;221&YC%12=K%@2LQG%TD3U?1?&T<%12Q6QC%SI21G&T;%11QF%SL2J1%QF241%QG281%QH2;1%QI2>1%QJ2B1%QK2E1%QL2J1%QM2L1&T7%S<1QD%24RJ1Q6Q>%S92ULS6%S:2UMS1%T:221%T:23TL%I231%R6231&W=%S@2V3S2&RL&R?%11S@%311%6251%UC3V@1TN&RM%61R>%211%;2:1%UH3VE1T3%V12UKS>%UJ3VG1T5&W<%12V7?%UM3VJ1T8&YB%QF1V1%221C%V13VN1T<%RM251%RN291%RO2<1%S02B1p0K1phLVL1%S32Q31%S42Q71%S52R81%S62R?1%S72RB1%S82RE1%S92RI1%S:2RL1%S;2S21tdBW@S=1tR>W<SC1thDSNSL1p0T01p0T51p0T91tfFW<T>1tfHWCTA1teNWDTE1p0TN1p0U51p0U:1p0UE1p0V21p0V91p0V@1p0W21pRJWA1pf>WA1pcLWI1pf<WC1pRHWE1pW:WK1pR<X21pfNX41pg0X51pfLX71pdJX91peBX;1pd>X=1").
Proof.
intros cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh len nZ n Hg GPo GM v E' cs1.
assert (Hnoholes : Forall (fun m => is_hole m = false) (a_maps cs)).
{ unfold no_holes in Hnoh. apply Forall_forall. intros m Hm. pose proof (proj1 (forallb_forall _ _) Hnoh m Hm) as X. apply negb_true_iff in X. exact X. }
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
assert (HnZpos : 0 < nZ) by lia.
pose proof (u64_range a) as Ra.
pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
pose proof (ext1_agree'' E v (Z_to_bv 64 (bv_unsigned a / 4096))) as Hag. fold E' in Hag.
destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fvis & Fbrk & Ffd & Fle). fold v in Fsr, Fkn, Fmaps, Fvis, Fbrk, Ffd, Fle.
assert (HC' : CSOK E' cs R FULL model) by (eapply cs_ok_agree'; [exact Hag | exact Hfresh | exact HC]).
assert (Hag0 : env_agree nx0 E E') by (eapply env_agree_le'; [exact Hag | exact Fle]).
assert (Hv : ev E' v = Z_to_bv 64 (bv_unsigned a / 4096)) by apply ext1_at.
assert (HneE' : edenot E' ne = n).
{ rewrite (HneE E'); [exact Hne|]. symmetry. eapply edenot_agree'; [exact Hag|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }
destruct (null_grant_facts E' cs R FULL model a nZ HC' Hg HnZpos HnZal) as (Hal & H4096 & HaT & HT & Un & Hrf & Himg_a & Hapart).
fold n in Un, Hrf.
destruct (null_kfacts_ok E' cs R FULL model ne nlo nhi a n nZ (MR E' cs model' FULL') HC' HML Hv HneE' Un ltac:(lia) HnZpos HnZal Hg) as (KNEW & Hbase & VLH).
pose proof (grant_new_facts E' cs R FULL model a n nZ HC' Hrf Un HnZpos Himg_a HaT) as NEW.
destruct (grant_cs1_ok E' cs R FULL model kd a n nZ model' FULL'
(sr_upd (s_regs (a_ss cs)) 10 (null_base cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) a)
(null_kfacts cs ne nlo) (null_base cs) ne nhi eager (a_ylo cs) (Datatypes.S v)
HC' Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
- apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | lia | exact Hbase].
- exact Hbase.
- exact HneE'.
- exact KNEW.
- exact Hkind.
- exact Hkfog.
- lia.
- exact Hbudget.
- lia.
- intros m Hm Hk. exfalso. pose proof (proj1 (Forall_forall _ _) Hnoholes m Hm) as X. congruence.
- split; [exact HC1|]. split; [exact Hbase|]. split; [exact HneE'|]. split; [exact Un|]. split; [exact Hag0|]. split; [exact Hag|].
split; [exact Hv|]. split; [destruct VLH; repeat split; lia|]. split; [exact Hapart|].
intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & N3 & N4 & _).
split; [|auto]. rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma null_first_run : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q;'WN'='U?%211'Q4&T7r6r5r4r3%544321&YCz%2215'J'A'D%12==%311&UIr7%211(5(C%14DD@?%3281%<3851'N&YA&Y>%12:H%321H%42H<%6221p081p0F1p0J1pe0Q11pe4Q21pfFQ31pf0Q41pf@Q61pR<Q:1").
Proof.
intros E ms lo n flo fhi Hap Hn Hfr.
destruct (PlaceLemmasK.first_run_In ms flo fhi Hfr) as (rn & k & -> & Hin).
eapply runs_apart_grant; eassumption.
Qed.
Lemma null_low_fact : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QL'WN'>'\5yR0%211'Q4'Ay8%611%311p061'J&WOr8r7%3221&\4&Y?&\6r6%22A1+TP0%5221%72D1%=3D91&YAr3%92H=%;217%4231&Y>%=2LB%221Br5%9221%:2EF&X<vY8r<(WH(WGr;%211&YI%12NO%L21H%734K1%;4:9>1p0=1p0?1p0E1p0K1pW2Q:1phHQ@1pf0QA1pg0QB1pfHQC1pcLQE1phDQI1pR<QK1").
Proof.
intros E v a nZ nlo lo vlo M Hv Hvlo Hlo Hnlo. pose proof (u64_range a) as Ra.
cbn [kentry_ok edenot]. rewrite Hv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite u64_lit by lia. split; [exact Hvlo|]. apply Z.div_le_mono; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma null_high_fact : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QK'WN'>'\5yR0%211'Q4'Ay8%611%311p061'J&WOr6r5%3221&\4&Y?&\6r4%22A1+TP0%5221%72D1%=3D91&YA%82G<%:216r3%4221%<2KA%62A1&YEr7%@2O1%321>z%J3Q021&X<vY8r:(WH(WGr9%211&W5%12=I%6331Q2%:498Q21p0<1p0C1p0F1p0L1pW2Q;1phFQA1pe:QB1pcLQD1phDQH1pR<QJ1").
Proof.
intros E v a hi vhi M Hv Hvhi Hhi Hal. pose proof (u64_range a) as Ra.
cbn [kentry_ok edenot]. rewrite Hv. unfold zcdiv'.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite u64_lit by lia. split; [|exact Hvhi]. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma null_child_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QA'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'X2'W9vY8v0vQ?vY9vZ0vQ:r6r5r4r3r2%<;;:987654321&X<r8r1%34?216pW2D1&VMr7(9&V8%113%33H=1%6251%I;HGFEDC;1BA@p091p0?1pRLM1pf<O1pRHQ11pW:Q71pdBQ>1pR<Q@1").
Proof.
intros E cs1 R FULL model K HC HK. apply cs_ok_set_kn; [exact HC|].
constructor; [apply HK | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
Qed.
Lemma null_high_vbot : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "F'Q4&YAr1r2%3221'J&YEr3+TP0%3221z%63;21&W5%1265&Y?r4%2218%@241p071p0?1pe:D1pcLE1").
Proof.
intros a hi Hhi Hal. unfold zcdiv'.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Lemma null_low_vtop : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "L'Q4&YA&Y>r4r3%3221r1%6221%7245zr6%:221&Y?r7+TP0%3221&YIr5%22?1%7215%C251p0:1p0>1p0@1pf0H1pg0I1pfHJ1pcLK1").
Proof. intros a nZ nlo lo H1 H2 H3. apply Z.div_le_mono; lia. Qed.
Lemma kmem_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "RE'WN'\5yR0%211'Ay8%511%311phL51'X0'Q4'J&X;r6(WKr4z%3221%6251r2%93:21&X:r7%2218%=3>15'I&YA%12;<&YC&YH+2+R0%3221%52B1%9271&Y>r5%22H1%<216r8&\6r1%22Q81%A241%925F%A231%E231r<%11M(5&\4%12Q>Q3%32Q>1%Q:3Q>51p081phLQD1&X=vY8r;(9'X2(WIr:%QA21Q?r9%4221(WJ%1243(@%119%;3:31%<3;61%@4?I>1p0B1p0Q41p0Q@1p0Q:1p0QE1p0QJ1pfFR51pf0R61pfLR81pd4R91pW2R;1pR<RD1").
Proof.
intros E M b ne lo n Hs Hn Hlo Hn0 Hhi BYTE.
assert (Hfl : flat E (SA b 0) (elenZ E ne)) by (unfold flat; rewrite Hs, Hn; lia).
constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; rewrite ?Hs, ?Hn.
- intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
intros x Hx. rewrite u64_lit in Hx by lia. unfold wview. rewrite (BYTE x) by lia. discriminate.
- intros i Hi. apply BYTE. rewrite u64_lit by lia. lia.
Qed.
Lemma kimg_in_hull_pure : forall k,
Forall (fun K => match K with KImg _ _ => False | _ => True end) k -> kimg_in_hull A k.
Proof.
intros k H. unfold kimg_in_hull. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) H K Hin) as HK. destruct K; try exact I. destruct HK.
Qed.
Lemma grant_vis_add : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "TE'WN'U:'X0&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r;r:r6r5r4%<;;:987654321'J%E1M&W1r9r8&7'X2(9(WI(WKz%2281%4218(WJ%123:(@%11:%:3;31%;3<61&V8%11J%@3?31%D6Q1Q0LCB1(5%12QDM%I3H31&W?r<%911%32Q81&WMr>%221Q6%Q13QG1Q5r?%521Q9%Q43QJ1Q8&\6r7%22QN1%Q83QF1Q<&YA%12Q04&Y>%72R3QA%221Q9&YH+2+R0%3221%9251'I%?2R;Ir1%A2R=1%>231&YC%>25QN%2241%8241'8&W=r2%J2RF1&RL&R?%11Q3%311%7251(F%R63:21&RM%116%<2:1(:%R;3?21rE%RE21?%R>3B14%L241%M2:1p0F1phLS81r=%Q?2S;1%Q<21O%Q;22RL%O2Q11%Q5231r@%11L&\4%12S?RB%R62S?1%RN3S?41p071phLSF1rC%S?;S>S=S<S;S:S9F19R0R3p031p0B1p0QC1p0QL1p0QO1p0R41p0R81p0R=1p0RB1p0S=1pfHSK1pfFT41pcLT51pf<SO1pRHT11pW:T71pfLT>1pd8T?1pdDTA1pdBTB1pR<TD1").
Proof.
intros E cs1 cs2 base ne R FULL model a n nZ HC1 Hva Hkh Hbase Hne Un HnZ Hhi NEW ZERO.
pose proof (u64_range a) as Ra.
eapply vis_add_sound'; [exact Hva | exact HC1 |].
destruct (vis_add_inv cs1 base ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
apply Forall_app. split.
-
eapply (kmem_ok E _ base ne (bv_unsigned a) nZ); [unfold estart; cbn [a_base a_off]; rewrite Hbase; lia | unfold elenZ; rewrite Hne; exact Un | lia | lia | lia |].
intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
unfold Mr, mrestrict, hid. rewrite N3. cbn [orb].
unfold vis. rewrite N1, N2. cbn [negb andb].
assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
{ unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. unfold uE. rewrite Hbase, Hne, Un.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
rewrite Hal. rewrite !orb_true_r. cbn [negb]. apply ZERO. exact Hx.
-
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
+ intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
+ intros y Hy. apply hid_hull'. exact Hy.
Qed.
Lemma gap_weight_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "L'Q4'='D'\5yR0%211%4211%611'J&TAr2r1%3221&Y>&WB%114&YF&YG&<%12=8%311+SoO%92<1%7231%;291%A3I=1peHC1pfHK1").
Proof. induction l as [|[b sz] l IH]; cbn -[Z.of_nat Z.add Z.mul]; [lia|]. rewrite IH. rewrite Nat2Z.inj_succ. cbn [snd]. lia. Qed.
Lemma gap_ok_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QI'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r7r6r5r4r3%<;;:987654321'J'8&UM%13>95(F%53421'I&YAz%221;%32<=%5221'K&XIr1%23E1C%@3?1<qcLQ71%62Q81p081p0?1p0F1pfHQ41pfNQ51pf<Q71pRHQ91pW:Q?1pd>QF1pR<QH1").
Proof.
intros E cs R FULL model nhi nZ HC Hg HnZ. unfold gap_ok in Hg. apply Z.leb_le in Hg.
pose proof (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC) as T.
assert (L : (length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= n_res A + length (a_maps cs))%nat).
{ rewrite length_app, (co_res _ _ _ _ _ _ _ _ _ _ _ HC), RES_len'. pose proof (maps_match_length E _ _ (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). lia. }
assert (GW : gw_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs).
{ pose proof (gap_weight_sizes nZ (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) as G1.
rewrite gap_weight_eq in G1. lia. }
destruct (free_gap_of_totals (m_vmmaps model) nZ (a_totsz cs) ltac:(lia) GW) as (g & Hal & Hfl & Hc & Hfree & Hpl).
{ rewrite FLOOR_eq, CEIL_eq.
assert (0 <= a_totsz cs).
{ assert (0 <= sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))); [|lia].
clear. induction (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) as [|[b sz] l IH]; cbn; [lia|]. pose proof (u64_range sz). lia. }
set (len1 := length (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) in *.
set (len2 := (n_res A + length (a_maps cs))%nat) in *.
assert (Z.of_nat len1 * (nZ + 4095) <= Z.of_nat len2 * (nhi + 4095)) by nia. nia. }
pose proof bottomup_floor_val as Hfv. pose proof alloc_ceiling_val as Hcv.
assert (Hg64 : 0 <= g < 2 ^ 64) by lia.
pose proof (alloc_top_eq E cs R FULL model HC) as AT. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]].
exists (Z_to_bv 64 g). unfold grant_ok_na_pin. rewrite u64_lit by lia.
rewrite Hfree. unfold page_size in Hal |- *.
rewrite (proj2 (Z.eqb_eq _ _) Hal). rewrite (proj2 (Z.ltb_lt 0 g)) by lia.
rewrite (proj2 (Z.leb_le _ _)); [reflexivity|]. rewrite AT. unfold sp_window_lo in *. lia.
Qed.
Lemma budget_slack : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QD'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'W9vY8v0vQ?vY9vZ0vQ:r6r5r4r3r2%<;;:987654321'J'8&UA%13=95(F%53421&YA&Y>&RJ%11=%321=&RK&R?%11A%311%9251p0;1p0B1pdLQ01pf<Q21pRHQ41pW:Q:1pd>QA1pR<QC1").
Proof.
intros E cs R FULL model extra HC Hb. unfold budget_ok in Hb. apply Z.leb_le in Hb.
pose proof (vm_backing_used_le (ALLOW E cs) model (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (A_wf_allowA' E cs)).
pose proof (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). pose proof (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC).
rewrite (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). lia.
Qed.
Lemma lazy_interior_fresh : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QA'\5yR0%211'J'Q4&YE&\6r2%2271+TP0%5221z%93821&YCr3%92>1%3251&YA&Y>r5%>2C1r4%@2E1%5231&YH+2+R0%3221%;251'='D%12MM%311&R9r6%221@(9(C%14Q4Q44C(@%119%53:31%Q73:71p0?1p0L1p0Q11p0Q21pfFQ=1pcLQ>1").
Proof. intros. apply lazy_interior_aligned; unfold page_size; assumption. Qed.
Lemma refuse_eq : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'U:'J&VGr1%211&W4&V=&Y>&VF%116+4%4221&X7&X5&U5%11<%311u:(WF&TG%211%93541&V8%11D&VC%11F%D4?531%F2H1%K3LH1pd>M1").
Proof. reflexivity. Qed.
Lemma refuse_pc : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ">'U:'J'Q4&VF&VGr1%211%411&Y>%614+4%3221%;3:51pd>=1").
Proof. reflexivity. Qed.
Lemma refuse_nxt : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK ";'U:'J'>&VC&VGr1%211%411%513%83721pd>:1").
Proof. reflexivity. Qed.
Lemma refuse_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q?'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321r6&VG%118&Y0&\4&YGu:%211%42Q01&R6&R2%211%93A41%J;IHGFED=;1A@p0?1pf<M1pRHO1pW:Q51pd>Q<1pR<Q>1").
Proof.
intros E cs R FULL model HC. rewrite refuse_eq.
eapply cs_ok_frame'; [exact HC | apply same_but_materialized_refl | exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | | reflexivity | exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | intros; reflexivity].
cbn [s_regs mk_ss]. apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia |].
cbn [edenot]. rewrite errno_ret_ENOMEM. reflexivity.
Qed.
Lemma refuse_cont : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "SB'U:'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3&Y5'W9vY8v0vQ?vY9vZ0vQ:r5r6r4r3r2%<;;:987654321&YAz&VFr7%211%5241&YC&Y>r8%711+4%4221&YH+2+R0%3221%:251'I&X?v[Ar<%3321I&VCr=%211%7315M%9251&VGr>%211%Q;;Q:Q9Q8Q7Q6Q5Q41Q2Q1Q0'J&QA&R;%11Q5r;%311%63531'Y7v[O&W8r@%?11%Q911%45QHQA1QBQ@%74QI61:p091p0A1p0F1pf>R01pRJR21pW<R81pR>R?1(QN&XO&T@&Y0(\3+:(H%33RE21&R6&R2%211%83QH41&Y2&\4r:%R211%32RL1%521QL&Y1%11RD%C5B93R61%E21R?%Q54RGQ41RAp0H1p0QM1p0R91p0R@1pcHRN1pf<S01pRHS21pW:S81pR<S?1pd>SA1").
Proof.
intros cs E R FULL model TA HC Hp0 Hp4 HKA.
specialize (HKA E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (errno_ret ENOMEM)) FULL model
(conj (env_agree_refl' _ _) (env_agree_refl' _ _)) (refuse_ok E cs R FULL model HC) eq_refl).
unfold cfg_of in HKA. rewrite refuse_pc, <- bv5_10 in HKA. rewrite (v_addi_pc (pc cs) Hp0 Hp4). exact HKA.
Qed.
Lemma page_aligned_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'WN'\5yR0%211'Ay8%511%311p051'='X2%211'X0&X=vY8r4r3r2%544321'J'8&VD%1265(F%53421'Q4&YE&\6&WMr6%221>%42M1+TP0%7221z%@3:21p0<1p0C1pdFJ1pe@L1pW2Q01pR<Q91").
Proof.
intros E M k e HK H.
assert (GEN : 12 <= ealign k e -> bv_unsigned (edenot E e) mod 4096 = 0).
{ intros Hle. destruct (ealign_sound SEGS E M k e HK) as [Hr [q Hq]]. rewrite Hq.
replace (2 ^ ealign k e) with (2 ^ (ealign k e - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
unfold page_aligned in H. destruct e as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact H).
apply Z.eqb_eq in H. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
rewrite Z.mod_mod_divide; [exact H | exists (2 ^ 52); reflexivity].
Qed.
Lemma fixed_args_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "T1'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'X0'W9vY8v0vQ?vY9vZ0vQ:r;r:r9r8r7%<;;:987654321'J'D%12@A%221A%321C%421D%K11&UJ%13C>:(5(Cr6r5%34KL21r4%54=M21r3%74>Q021r2%94?Q221%;2?1%E3?=1'I&X6&VHr<u:%3221%511%C4Q;Q<OB%N3L21%N2MQ>%QE11&V?%119%I4QAQBGE%J4Q2QC1D%L261%Q63641&YE&\6&WMr=%221@%42R41+TP0%7221z%Q@3QO21&YC%1236'N&YA&Y>%=2<Q:%?2R?1%32<1&UO%11R5%7231&UN%11R8%:21B%<241%;2DQ@%=21R4&XN&\4&YG%11Q;%32S01%52R=1%R83RO1M'8&UK&V8%11QC%341R?R2R1(F%R?3621%QJ281%QK2@1%QL2C1%QM2Q11%QN2Q41%QO2Q?1%R02QH1p0R21p0RI1pfNS81pg0S91pfLS91pg8S;1pd4S;1phBS=1pf<S?1pRHSA1pW:SG1pd>SN1pR<T01").
Proof.
intros E cs R FULL model top b off ne nlo nhi HC H. unfold fixed_args in H. pose proof HULL_lt as HL. unfold hull_lt in HL.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof HULL_ok' as (HU0 & HU1 & HU2 & HU3).
destruct (split_lit (reg cs 10)) as [b0 off0] eqn:Hsp.
destruct (mmap_len cs) as [[[ne0 nlo0] nhi0]|] eqn:HML; [|discriminate].
destruct (xlo (kn cs) (reg cs 10)) as [alo|] eqn:Hxl; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [ahi|] eqn:Hxh; [|discriminate].
match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hflat].
injection H as -> -> -> -> ->.
apply andb_prop in Hc as [Hc Htop]. apply andb_prop in Hc as [Hc Himg]. apply andb_prop in Hc as [Hpa Hpos].
apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Hxl). pose proof (xhi_sound SEGS E _ (kn cs) _ ahi HK Hxh).
assert (Hhull : bv_unsigned (edenot E (reg cs 10)) + bv_unsigned (edenot E ne) <= img_lo A \/ img_hi A <= bv_unsigned (edenot E (reg cs 10))).
{ apply orb_prop in Himg as [Himg|Hoff].
- apply Z.leb_le in Himg. right. lia.
- unfold off_image_x in Hoff. pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) HK Hoff) as D.
destruct (APSK.flat_x_sound SEGS E _ (kn cs) b off ne HK Hflat) as (F1 & F2 & F3).
pose proof (APSK.u_of_split E (reg cs 10) b off Hsp ltac:(lia)) as U.
unfold estart, elenZ in D. cbn [a_base a_off] in D. rewrite !edenot_lit in D. rewrite !u64_lit in D by (unfold KHI in *; lia).
unfold estart in U. cbn [a_base a_off] in U. lia. }
repeat split; try lia.
- eapply page_aligned_sound; [exact HK | exact Hpa].
- apply (reg_sound' E cs R FULL model); [exact HC | lia].
- exact Hflat.
Qed.
Lemma split_flat_estart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R7'WN'\5yR0%211'Ay8%511%311p051'='X2%211'X0'Q4&X=vY8r7r6r5%544321'J'D%12:9&X6%116(Cr4r3%34@?21%93751'8&UK%14@>65(F%>3421'I&X;r:(WK%12FE%4231&\6&WM%126K%32Q:1%I3Q051&YA&Y>%62;F%82Q?1%32:1&YH+2+R0%3221%9251&YCz%2219%H241%I2?1p0K1p0Q11p0Q<1pfFQD1pg8QD1pd4QF1pdFQG1pe@QI1pW2QM1pR<R61").
Proof.
intros E M k e b off n HK Hsp Hfl.
destruct (APSK.flat_x_sound SEGS E M k b off n HK Hfl) as (F1 & F2 & F3).
pose proof (APSK.u_of_split E e b off Hsp ltac:(lia)). repeat split; lia.
Qed.
Lemma region_free_of_apart : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "S>'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'X0'Q4'W9vY8v0vQ?vY9vZ0vQ:r:r9r8r7r6%<;;:987654321'J'8&V@&U4%11:%311(F%73621&Y='U?&X4&V8r<%211&U<r1%211z&U>%114%:77HGF431qf2<1r;%D11%@3?31%I3H1C&X;r=(WK%12Q1Q0%4231&\6r5%22QI1%Q23Q@41&X:r>%221Q8%Q63QD15'N&YA&Y>%;2R2Q=%<2R3Q=%3221&UO%11QI%7231&UN%11QL%:218%<241&RG&7'D%12R>R>&RN&R?%11Q>%311&RL%113%93731%;31R3R2%R03QO1QJp0>1p0L1p0Q11p0Q;1p0QN1p0R71pfFRN1pf0RO1pfLRH1pg8RH1pd4RJ1pf<RL1pRHRN1pW:S41pd>S;1pR<S=1").
Proof.
intros E cs R FULL model b off ne lo n HC Hnf Hall Hs Hn Himg.
rewrite region_free_app. apply andb_true_intro. split.
- apply reserved_free_hull_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg].
- rewrite (proj1 (maps_match_exact' E _ _ Hnf) (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)). apply RefNodes.region_free_intro. intros bm sm Hin.
apply in_map_iff in Hin as (m & Hm & Hinm). unfold amap_den in Hm. injection Hm as <- <-.
pose proof (proj1 (forallb_forall _ _) Hall m Hinm) as Hap.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hap) as D.
unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D, Hn. rewrite Hs, Hn in D. lia.
Qed.
Definition fixed_cs1 (cs : acs) (kd : mkind) (eager : bool) (ne : expr) (nhi : Z) : acs :=
let k := kn cs in
let m := AM (reg cs 10) ne kd in
let ksh := if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A k [m] (fst p) (snd p)) (a_vis cs) else [] in
add_entry cs (s_regs (a_ss cs)) (ksh ++ kn_grant_filter A k (a_maps cs)) (nxt cs) m nhi eager (a_ylo cs).
Lemma shadow_facts_new_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "T6'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'Q4'X0'W9vY8v0vQ?vY9vZ0vQ:r;r:r9r8r7%<;;:987654321'J&\6r6%22K1r5%53D21&WMr=%2214%93Q01;&YA&Y>%;2Q4@%221?&TF%5221r?&VHr>u:%3221%?251%F3Q=1K'T3(TKr<%352Q0O1L&T2%1543Q2:N'I%M2QF<r1%O2QH1%G231&YC%H25:%2241%8241'8&W=r2%Q82R11&RM&R?r@%211%411%8261(:%QA3;21rD%QK21;%QD3>14%H241p0A1phLR>1&X=rC&W6rB%26R7R431R1R0&Y<'D%12R=R='X2&VN&V8%11:(9'U?(TE%QF2>QD%231Q?Q@(@%115%73631&;%13RKRKQ>&E%13RMRMQ@%?5RK=531qg:B1&U8%11H%G4ED31%M4S1LI1p0O1p0QK1p0QN1p0R31p0R;1p0RB1p0RG1p0RN1pRJS?1pf>S?1pfLS>1pfHS@1pfFSI1pcLSJ1pf<SD1pRHSF1pW:SL1pd>T31pR<T51").
Proof.
intros E cs R FULL model a n nZ ne model' FULL' HC Un Hne HaC Hra GPo [GM1 GM2] NEW.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (u64_range a) as Ra. pose proof SHADOW_ok' as SO.
unfold know_ok. apply Forall_flat_map. apply Forall_forall. intros p Hp.
unfold shadow_facts.
destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh.
match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hjust; [|constructor] end.
unfold shadow_of in Hsh.
destruct (split_lit (eadd (mkSrl (kn cs) (fst p) 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection Hsh as -> -> <-.
destruct (APSK.shadow_facts_holder SEGS A HS XN XE XB SHADOW_ok 0%nat E _ (kn cs) [AM (reg cs 10) ne KRWLAZY] (fst p) (snd p) sb sk HK Hss Hjust)
as (_ & m & Hmin & _ & _ & I1 & I2).
destruct Hmin as [<-|[]]. cbn [am_base am_len] in I1, I2. rewrite Hne, Un in I2. rewrite Hra in I1, I2.
pose proof HaC as HaC'. unfold CEIL in HaC'.
assert (Usn : bv_unsigned (edenot E (mkSrl (kn cs) (snd p) 3)) = bv_unsigned (edenot E (snd p)) / 8).
{ rewrite (mkSrl_denot SEGS E _ (kn cs) (snd p) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
rewrite Usn in I2.
set (S0 := bv_unsigned (edenot E sb) + sk) in *.
pose proof (u64_range (edenot E (fst p))) as Rb. pose proof (u64_range (edenot E (snd p))) as Rn.
pose proof (u64_range (edenot E (mkSrl (kn cs) (snd p) 3))) as Rsn.
assert (HS0 : S0 = shadow_off A + bv_unsigned (edenot E (fst p)) / 8).
{ pose proof (APSK.split_lit_denot E _ sb sk Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
apply (f_equal bv_unsigned) in D. rewrite u_add64 in D.
rewrite (mkSrl_denot SEGS E _ (kn cs) (fst p) 3 (Z_to_bv 64 3) HK) in D by (rewrite u64_lit by lia; reflexivity).
rewrite u_srl64 in D. fold S0 in D.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite !u64_lit in D by (unfold CEIL in *; lia).
change (2 ^ (3 mod 64)) with 8 in D.
rewrite (Z.mod_small (bv_unsigned (edenot E (fst p)) / 8 + shadow_off A)) in D by (unfold CEIL in *; lia).
unfold CEIL in *. lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (BYTE : forall y : word, S0 <= bv_unsigned y < S0 + bv_unsigned (edenot E (snd p)) / 8 ->
MR E cs model' FULL' y = Some (Z_to_bv 8 0)).
{ intros y Hy.
assert (Hya : bv_unsigned a <= bv_unsigned y < bv_unsigned a + nZ) by (clear -Hy I1 I2; lia).
destruct (NEW y Hya) as [N1 N2].
assert (Hsh2 : in_sh A E cs (bv_unsigned y) = true).
{ unfold in_sh. apply existsb_exists. exists p. split; [exact Hp|]. unfold sh_lo, sh_hi, uE.
apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt].
- lia.
- Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (V : VIS E cs model' y = true).
{ unfold vis. rewrite (gp_maps _ _ _ _ _ GPo), (gp_noacc _ _ _ _ _ GPo). cbn [kind_none].
rewrite in_ivs_cons. cbn [fst snd]. rewrite Un, N1.
rewrite (proj2 (Z.leb_le (bv_unsigned a) (bv_unsigned y))) by lia.
rewrite (proj2 (Z.ltb_lt (bv_unsigned y) (bv_unsigned a + nZ))) by lia.
unfold in_allow. rewrite Hsh2. rewrite !orb_true_r. cbn [andb orb negb]. rewrite ?orb_true_r. reflexivity. }
unfold Mr, mrestrict, hid. rewrite N2, V. cbn [orb negb].
rewrite (GM2 y) by (rewrite Un; exact Hya). reflexivity. }
assert (Hfl : flat E (SA sb sk) (elenZ E (mkSrl (kn cs) (snd p) 3))).
{ unfold flat, estart, elenZ. cbn [a_base a_off]. fold S0. rewrite Usn. unfold CEIL in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl;
unfold estart, elenZ; cbn [a_base a_off]; fold S0; rewrite Usn.
- intros d w Hd Hdw. destruct w as [|w']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in *; lia); unfold CEIL in *; lia|].
intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in *; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
- intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in *; lia). lia.
Qed.
Lemma fixed_pre : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "T<'U:'Q4'X0'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r4r;r3r2r1%<;;:987654321'J'D%12MN%221N%321Q0%421Q1%I11&UJr<%23D1>(5(Cr:r9%34Q9Q:21r8%54>Q;21r7%74?Q>21r6%94@Q@21%;2@1%F3@=1&YA&TF%22A1&WM&VHr>u:%3221%52>1&\6r?u;%8221%:2E1%52QK1&RE%11Q9&\4%12QOQ;'I%A2Q@?%Q<3R11Q>%=2R3Q?%Q>3R:1QA&X;(WKr@%221A%42QH1%D2R:QJ%QE3RA21&YE+TP0%2241z%QJ3RF21&YC%1238'N&Y>%12;R2&UO%11R<%Q;231&UN%11R?%Q>21A%9241rA%QA291&XN&YG%11Q>%Q42S41%42R11%R>3S31RD%I2RBH%R@3S<1G%F2HRD%QK2RER:%Q9221%Q:241%Q;271%Q<2>1%Q=2A1%Q>2L1%Q?2O1%Q@2Q51%QA2Q=1%QB2Q@1tfFSBQD1tfHSJQG1teNSKQJ1td0SER11p0R81p0R<1p0S41pf<SB1pRHSD1pW:SJ1pR<T11pfNT41pg0T51pfLT51pg8T71pd4T71phBT91pd>T;1").
Proof.
intros cs top b off ne nlo nhi E R FULL model HC HFA Htop addr len nZ n.
destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & HtopA & R10 & Hflat).
fold addr in Hal, Hpos, Himg, HtopA, R10.
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
destruct (split_flat_estart E _ (kn cs) (reg cs 10) b off ne HK Hsp Hflat) as (Hest & Hfl2 & Hfl3). fold addr in Hest.
pose proof (u64_range addr) as Ra.
assert (Un0 : bv_unsigned n = nZ).
{ subst n. apply u64_lit. split; [lia|]. pose proof (u64_range (Z_to_bv 64 nZ)) as Rn. unfold CEIL in Htop. lia. }
split; [exact Hne|]. split; [exact Un0|]. split; [exact Hest|]. split; [exact Hal|]. split; [exact Hpos|].
split; [rewrite Hne, Un0 in Himg; exact Himg|]. split; [lia|]. split; [exact R10|]. split; [exact HnZal | lia].
Qed.
Lemma maps_match_unhole : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'WN'='U?%211'D'\5yR0%211%4211%811&L&W@r4r3r1%43321&W0r2%2251%83715%:251peH<1pe8D1pf@D1pR<H1").
Proof.
intros E ms h. unfold unhole. induction ms as [|m ms IH]; intros l; [cbn; tauto|].
cbn [List.map maps_match].
destruct (is_hole m && amap_eqb m h)%bool eqn:Hc.
- apply andb_prop in Hc as [Hh _].
assert (Hf : is_fog m = true) by (unfold is_fog, is_hole in *; destruct (am_kind m); cbn in Hh |- *; congruence).
rewrite Hf. cbn [is_fog is_tok_kind am_kind am_len].
split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
- destruct (is_fog m).
+ split; (intros [H|(iv & l' & H1 & H2 & H3)]; [left; apply IH; exact H | right; exists iv, l'; split; [exact H1|]; split; [exact H2| apply IH; exact H3]]).
+ split; (intros (l' & H1 & H2); exists l'; split; [exact H1 | apply IH; exact H2]).
Qed.
Lemma same_val_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q:'WN'\5yR0%211'Ay8%511%311p051'='X2%211'X0&X=vY8r5r4r3%544321'J'8&VLr2%23761(F%63521'Q4&\6&WMr7%221>%42M1%423?%62O1%?3831p0:1p0B1pd4I1pcLJ1pe@L1pW2Q01pR<Q91").
Proof.
intros E M k a b HK H. unfold same_val in H.
destruct (expr_eqb a b) eqn:He; [apply expr_eqb_eq in He; subst; reflexivity|].
destruct (lin_ge0 k [(a, 0)] [(b, 0)]) eqn:H1; [|discriminate].
pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as X1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H) as X2.
cbn [xt_den] in X1, X2. lia.
Qed.
Lemma find_hole_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R4'WN'\5yR0%211'Ay8%511%311p051'='X2%211'U?%411'X0&X=vY8r7r6r5%544321'J%B1:&UHr4r3%348721(5r2%22A1%93841'I&Y:%13E8?'8&V4%11;(F%A3421'Q4&WCr9&U<%11B%4231&\6&WM%126L%32Q>1%L3:51&U>%11J%<2;1%72<M%92QD1%Q23@31%I271%J2C1%K2I1p0M1p0Q81pe8QA1pfLQ@1pcLQA1pf@QC1pe@QF1pW2QJ1pR<R31").
Proof.
intros E M k ms a ne h HK H. unfold find_hole in H. apply find_some in H as [Hin Hc].
apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hh H1].
split; [exact Hin|]. split; [exact Hh|]. unfold uE.
split; symmetry; [exact (same_val_sound E M k _ _ HK H1) | exact (same_val_sound E M k _ _ HK H2)].
Qed.
Lemma cs_ok_unhole : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q;'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'U?'W9vY8v0vQ?vY9vZ0vQ:r6r5r4r3r2%<;;:987654321r7&W3&W0&U4%11:%3217%52<1%D;CBA@?>71<;:p091pe8G1pf<I1pRHK1pW:Q11pd>Q81pR<Q:1").
Proof.
intros E cs R FULL model h HC.
assert (ELEM : forall m, In m (unhole (a_maps cs) h) ->
In m (a_maps cs) \/ exists m0, In m0 (a_maps cs) /\ m = AM (am_base m0) (am_len m0) KFOG).
{ intros m Hm. unfold unhole in Hm. apply in_map_iff in Hm as (m0 & Hm0 & Hin).
destruct (is_hole m0 && amap_eqb m0 h)%bool; [right; exists m0; split; [exact Hin | symmetry; exact Hm0] | left; subst; exact Hin]. }
destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
constructor; unfold with_maps0 in *;
cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn] in *; try assumption.
- apply (proj1 (maps_match_unhole E _ h _)). exact Xmaps.
- apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
[exact (proj1 (Forall_forall _ _) Xholes m Hin Hk) | cbn in Hk; discriminate].
- apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
[exact (proj1 (Forall_forall _ _) Xnone m Hin Hk) | cbn in Hk; destruct Hk; discriminate].
- apply Forall_forall. intros m Hm Hk. destruct (ELEM m Hm) as [Hin|(m0 & Hin & ->)];
[exact (proj1 (Forall_forall _ _) Xkinds m Hin Hk) | cbn in Hk; discriminate].
Qed.
Lemma CEIL_le_utop : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r5r4r3r2r1%<;;:987654321&YA&TF&WDr6%211%5241p071pf<E1pRHG1pW:M1pd>Q41pR<Q61").
Proof.
intros E cs R FULL model HC. pose proof (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as [_ [ISP _]].
pose proof (utop_bounds E) as UB. pose proof (utop_mod E) as UM.
pose proof (Z.div_mod (utop E) 4096 ltac:(lia)) as Du. rewrite UM in Du.
unfold CEIL, sp_window_lo in *. lia.
Qed.
Lemma mmap_fixed_grant_cs1 : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "W1'U:'='U?%211'V>'8'Q4'X0'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r6r@r5r4r3%<;;:987654321'J'D%12MN%221N%321Q0%421Q1%I11&UJrAr=%33E21(5(Cr<r;%34Q:Q;21r:%54?Q<21r9%74@Q?21r8%94AQA21%;2A1%G3A=1&YAr>&TF%3221&W3rCrB%3221r7%Q>;Q=Q<Q;Q:Q9Q8?2=1Q7&WM&VHrDu:%3221%52G1&\6rEu;%8221%:2N1%52R31&REr1%211&\4%12R83&RG&7%QD2R:R:&RN&R?%11Q:%311&RL%113%83731%:31R0>(F%QO3RL21&Y:rI%23S2C1&V4r2%211%R63S318'N&Y>%Q12ROQE%221R@&WC&U<%11R?%32Q@1%QG251&U>%11RC%72QD1%;251%QL21;%>261p0@1p0E1pf2SH1rG%RJ3SG1L&TOrK%211&TM%113%H231%I21R3%R:21S<p091&B&T6%11Q5&T5%11Q7%5231&?rH%211%S=3T:41&V5rJ%211(:%SB3T?21'T3r?%25IS3SKSJ1&T2rL%251S8RHRJ4'I&T1rOrN%S1221rMrF%65329E1&Y0&YG%11RN%RC2TL1%43S11SG%TC;TBTAT@T?T>T=RM61T;SN%RO2TMSJ%S02TNRI%SA221&YC%R324SK%2241%D241&W=%S72U5R;%RI1SC%RG11%4231%TC3U@1RE&RM%RN1SA%211%9281%TH3UE1Q7%U12R0RE%TJ3UG1Q9%Q2231%Q3291p0@1phLUC1%Q62I1p0Q81p0Q<1p0Q@1p0QF1p0R11p0R=1p0S71tfFULSE1tfHV4SH1teNV5SL1td0UOT31p0T:1p0TA1p0TF1p0U?1pRJUN1pf>UN1pf<UO1pRHV11pW:V71pR<V>1pfNVA1pg0VB1pfLVB1pg8VD1pd4VD1phBVF1pdJVH1peBVJ1pfDVL1pd>W01").
Proof.
intros cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 addr len nZ n Hrf Hholes Hbudget Hkind Hkfog GPo GM.
destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
fold addr len nZ n in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
assert (HaC : bv_unsigned addr + nZ <= CEIL) by lia.
pose proof (CEIL_le_utop E cs R FULL model HC) as CU.
assert (HaT : bv_unsigned addr + nZ <= utop E) by lia.
assert (HnZpos : 0 < nZ) by lia.
pose proof Himg as Himg_a.
pose proof (grant_new_facts E cs R FULL model addr n nZ HC Hrf Un HnZpos Himg_a HaT) as NEW.
destruct (grant_cs1_ok E (with_maps0 cs ms0) R FULL model kd addr n nZ model' FULL'
(s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)
(if mkind_eqb kd KRWLAZY then flat_map (fun p => shadow_facts A (kn cs) [AM (reg cs 10) ne kd] (fst p) (snd p)) (a_vis cs) else [])
(reg cs 10) ne nhi eager (a_ylo cs) (nxt cs)
HC0 Un HnZpos HnZal Hal Himg_a HaT Hrf GPo GM) as (HC1 & MROUT & MRSAME).
- apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | exact R10].
- reflexivity.
- exact Hne.
- destruct kd; cbn [mkind_eqb]; try constructor.
change (MR E (with_maps0 cs ms0) model' FULL') with (MR E cs model' FULL').
eapply shadow_facts_new_ok; [exact HC | exact Un | exact Hne | exact HaC | reflexivity | exact GPo | exact GM |].
intros x Hx. destruct (NEW x Hx) as (_ & N1 & N2 & _). auto.
- exact Hkind.
- exact Hkfog.
- lia.
- exact Hbudget.
- cbn [with_maps0 a_ylo]. lia.
- cbn [with_maps0 a_maps]. exact Hholes.
- split; [exact HC1|].
intros x Hx. destruct (NEW x Hx) as (N0 & N1 & N2 & _). split; [|auto].
rewrite (gp_maps _ _ _ _ _ GPo), in_ivs_cons. cbn [fst snd]. rewrite Un.
apply orb_true_iff. left. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma mmap_fixed_old_facts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "TI'U:'X0'Q4'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r4r:r3r2r1%<;;:987654321'J'D%12NM%221O%321O%421Q0%I11&UJr;&TF%33E21(5(Cr9%24Q:Q9C1r8%44>Q<21r7%64?Q=21r6%84@Q?21%:2@1%F3@<1'8&V@&U4r<%211%411(F%N3721&Y='U?&X4&V8r>%211r=&U<%11Q9z&U>%11Q<%:776AQ3431qf2<1%D18%?3>21%Q?3H1B&WM&VHu:%22@1%42Q51&RE&\6r?u;%8221%:2Q=1%52RA1%711'I&W3r@%Q711%3221%R?;R>R=R<R;R:R9R71QEQCQA&RG&7%R42RJRJ&RN&R?%11QG%311&RL%113%83731&\4%12S4R@%<33RB1%R@3QI1QC&Y:rA%QJ11%33QDRF1&V4%11RI%RG3R01QJ'N&YA&Y>r5%Q62SB1%321S3&WC%QI1S3%22QK1%8241%QI1S6%52QN1%:241%<219%>251p0@1p0D1pf2R91%Q=2J1%Q>2Q91tfHT7Q@1td0T2QI1p0QO1p0RA1p0RJ1p0SB1pf<T01pRHT21pW:T81pR<T?1pfNTA1pg0TB1pfLTD1pg8TD1pd4TF1pd>TH1").
Proof.
intros cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall addr nZ.
destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
split; [|split].
- destruct cs; exact HC.
- eapply region_free_of_apart; [exact HC | exact Hnf | exact Hall | exact Hest | unfold elenZ; rewrite Hne; reflexivity | rewrite Un; exact Himg].
- intros m Hm Hk. exfalso. unfold no_fog in Hnf. pose proof (proj1 (forallb_forall _ _) Hnf m Hm) as X.
apply negb_true_iff in X. unfold is_fog, is_hole in *. destruct (am_kind m); cbn in X, Hk; congruence.
Qed.
Lemma mmap_fixed_hole_facts : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "U7'U:'X0'Q4'U?'WN&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r4r;r3r2r1%<;;:987654321'J'D%12ON%221Q0%321Q0%421Q1%I11&UJr<&TF%33E21(5(Cr:%24Q;Q:C1r9%44>Q=21r8%64?Q>21r7%84@Q@21%:2@1%F3@<1%Q:1QB&UH&V8r=%211&U4%113&VHu:%2261%94641D%G2QM?%Q33<21'8&Y=&B&?&V4%11Q;%311&X4r?%D11r>&U<%11QBz&U>%11QE%9776JQ<431%?2;1qf2RA1&W0%L1:%221Q8%E3RE41(F%QL3H21&WM%Q02BO%22Q>1&RE&\6r@u;%Q6221%82QF1%52RL1%711'I&W3rA%Q?11%E21RA%4231%RK;RJRIRHRGRFRER11QOQMQK&RG&7%R@2S6S6&RN&R?%11R1%311&RL%113%83731&\4%12S@RL%<33RN1%RL3QH1Q1&Y:rB%R311%Q921RH%43SLS31%QJ1S5%S33QO1Q8'N&YA&Y>r5%Q72SN1%321S?&WC%QL1S?%22RB1%8241%QL1SB%52RE1%:241%<219%>251p0@1p0C1pf2T@1%Q>2J1%Q?2Q91tfHTDQA1td0T>QJ1p0QN1p0RH1p0S61p0SN1pf<T<1pRHT>1pW:TD1pR<TK1pe8TM1pfNTO1pg0U01pfLU21pg8U21pd4U41pd>U61").
Proof.
intros cs b off ne nlo nhi h E R FULL model HC HFA Hfh Hap addr nZ.
destruct (fixed_pre cs CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(lia)) as (Hne & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
fold addr nZ in Hne, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
destruct (find_hole_sound E _ (kn cs) (a_maps cs) (reg cs 10) ne h HK Hfh) as (Hin & Hh & Hhb & Hhn).
fold addr in Hhb. rewrite Hne, Un in Hhn.
destruct (proj1 (Forall_forall _ _) (co_holes _ _ _ _ _ _ _ _ _ _ _ HC) h Hin Hh) as [F1 F2].
rewrite Hhb, Hhn in F1, F2.
split; [apply cs_ok_unhole; exact HC|]. split.
- apply RefNodes.region_free_intro. intros b' s' Hin'. rewrite Un. destruct (F1 (b', s') Hin'); cbn [fst snd] in *; lia.
- intros m Hm Hk. pose proof (proj1 (forallb_forall _ _) Hap m Hm) as X. cbn beta in X. rewrite Hk in X. cbn [negb orb] in X.
pose proof (ranges_apart_x_sound SEGS E _ (kn cs) b off ne (am_base m) 0 (am_len m) HK X) as D.
unfold estart in D at 2 3. cbn [a_base a_off] in D. unfold elenZ in D. rewrite Hest, Hne, Un in D. unfold uE. lia.
Qed.
Lemma seps_map_disjoint : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q5'U?'D'\5yR0%211%4211p061'=%118'WA&Q2r4r3%34=821%511&Y:%13@45r5%33B61&M'J%13E4:%311&W>r8r6%211%31:%5221p071p0<1p0?1p0B1pf4Q11pf2Q21pf@K1pdNN1").
Proof.
intros f ms. induction ms as [|h t IH]; intros m m' Hs Hm Hm' Hne; [destruct Hm|].
cbn [map] in Hs. inversion Hs as [|p l Hf Hl]; subst.
destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
- exfalso. exact (Hne eq_refl).
- exact (proj1 (Forall_forall _ _) Hf (f m') (in_map f t m' Hm')).
- pose proof (proj1 (Forall_forall _ _) Hf (f m) (in_map f t m Hm)) as D. unfold iv_disjoint in *. lia.
- exact (IH m m' Hl Hm Hm' Hne).
Qed.
Lemma maps_match_disjoint : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "QC'WN'='U?%211'D'\5yR0%211%4211%811&W@r5r4r3%43321'WA%114&Y:r6%23A71r7%43C91'J'8&V3%117(:%53421&Mr8%83L1:%311&W>&W7r<r9%3221%4238%6221p081p0=1p0>1p0E1p0H1p0L1p0O1pf4Q<1pf2Q=1peHQ71pf@Q>1pR<QB1").
Proof.
intros E ms. induction ms as [|h t IH]; intros l m m' HM Hs Hm Hm' Hf Hf' Hne; [destruct Hm|].
cbn [maps_match] in HM. destruct (is_fog h) eqn:Hfh.
- assert (Hmt : In m t) by (destruct Hm as [<-|Hm]; [congruence | exact Hm]).
assert (Hmt' : In m' t) by (destruct Hm' as [<-|Hm']; [congruence | exact Hm']).
destruct HM as [HM|(iv & l' & -> & _ & HM)].
+ exact (IH l m m' HM Hs Hmt Hmt' Hf Hf' Hne).
+ inversion Hs as [|p l0 Hfa Hl]; subst. exact (IH l' m m' HM Hl Hmt Hmt' Hf Hf' Hne).
- destruct HM as (l' & -> & HM). inversion Hs as [|p l0 Hfa Hl]; subst.
destruct Hm as [<-|Hm]; destruct Hm' as [<-|Hm'].
+ exfalso. exact (Hne eq_refl).
+ exact (proj1 (Forall_forall _ _) Hfa (amap_den E m') (maps_match_In E t l' m' HM Hm' Hf')).
+ pose proof (proj1 (Forall_forall _ _) Hfa (amap_den E m) (maps_match_In E t l' m HM Hm Hf)) as D. unfold iv_disjoint in *. lia.
+ exact (IH l' m m' HM Hl Hm Hm' Hf Hf' Hne).
Qed.
Lemma overlap_sum_contained : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q;'='D'\5yR0%211%4211%611'Q4'WAr5%211&Y:(Cr4%24::51r6%53;21&YA&\6%12@4%3217&Y>r7%52D1%3215%82<1%92;A&XGr:%2317>&YI%12@9%?231p071p091p0?1p0D1p0K1pe:O1pf0Q01pgNQ41pd4Q51peHQ41").
Proof.
intros l b s lo hi Hs Hin H1 H2 Hlh. induction l as [|p l IH]; [destruct Hin|].
inversion Hs as [|p' l' Hf Hl]; subst. rewrite overlap_sum_cons. destruct Hin as [->|Hin].
- pose proof (iv_count_in_rng_le (b, s) lo hi Hlh).
assert (Z0 : overlap_sum l lo hi = 0); [|lia].
clear IH Hs. revert Hf Hl. induction l as [|q l IH2]; intros Hf Hl; [reflexivity|]. rewrite overlap_sum_cons.
apply Forall_cons_iff in Hf as [Hq Hf']. inversion Hl; subst.
rewrite (IH2 Hf' ltac:(assumption)). rewrite iv_count_in_rng_disjoint; [lia|].
unfold iv_disjoint, B, S in *. cbn [fst snd] in Hq. lia.
- pose proof (IH Hl Hin) as IH'. rewrite iv_count_in_rng_disjoint; [lia|].
pose proof (proj1 (Forall_forall _ _) Hf (b, s) Hin) as D. unfold iv_disjoint, B, S in *. cbn [fst snd] in D. lia.
Qed.
Lemma rekind_den : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "I'WN'='U?%211'J'D'\5yR0%211%4211%911&Q2&W7r3%211&VIr2r1%3221%84A:51%94B;64%A3;21pf2D1pf@D1pR<H1").
Proof.
intros E ms m. unfold rekind. rewrite map_map. apply map_ext. intros m'. destruct (amap_eqb m' m); reflexivity.
Qed.
Lemma in_rekind : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'='U?%211&Y:r1&VIr3r2%3221%63851'K'Ir5%:3<91'N'Jr4%23@=1(TE&U<%114&U>%116(TJ%63421%:3HC1%?291&M%11;%>3LGI%C221%A251%E2C1qf6Q01%H2Q11p0J1pf4Q31pf2Q41pf@Q41").
Proof.
intros ms m m' H. unfold rekind in H. apply in_map_iff in H as (m0 & Hm0 & Hin). exists m0. split; [exact Hin|].
destruct (amap_eqb m0 m) eqn:He.
- left. apply APSK.amap_eqb_eq in He. subst m0. auto.
- right. split; [|symmetry; exact Hm0]. intros ->. rewrite amap_eqb_refl in He. discriminate.
Qed.
Lemma covered_maps_subtract : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q4'='D'\5yR0%211%4211%611'Q4&XEr4%211&YAr3%2241'J'8&XB&RBr6r5%3321;%5219&6%725;&?&XC%137A>%311%6251%?3>81p0A1p0E1phLI1pe:J1pf0K1peHM1").
Proof. intros. apply (proj2 (proj2 (maps_subtract_sem l lo hi H H0))). Qed.
Inductive slarm := SlE | SlF | SlG | SlM.
Definition sl_nn (s : slarm) : bool := match s with SlG => true | _ => false end.
Definition sl_charge (s : slarm) : bool := match s with SlE | SlM => true | _ => false end.
Record slice_post (s : slarm) (addr n : word) (model model' : Model) : Prop := SP {
sp_maps : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model);
sp_res : vm_reserved (m_vmmaps model') = vm_reserved (m_vmmaps model);
sp_noacc : vm_noaccess (m_vmmaps model') =
(if sl_nn s then [(addr, n)] else [])
++ maps_subtract (vm_noaccess (m_vmmaps model)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n);
sp_lazy : m_vm_lazy model' =
match s with
| SlM => m_vm_lazy model
| SlF => (addr, n) :: maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
| _ => maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
end;
sp_mat : m_vm_materialized model' =
match s with
| SlM => m_vm_materialized model
| _ => List.filter (page_outside_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)) (m_vm_materialized model)
end;
sp_limit : vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model);
sp_brk : vm_brk (m_vmmaps model') = vm_brk (m_vmmaps model);
sp_sbrk : vm_start_brk (m_vmmaps model') = vm_start_brk (m_vmmaps model);
sp_mbase : vm_mmap_base (m_vmmaps model') = vm_mmap_base (m_vmmaps model);
sp_halted : m_halted model' = m_halted model;
sp_fds : m_fds model' = m_fds model;
sp_fs : m_fs model' = m_fs model;
sp_tid : m_tid model' = m_tid model;
sp_isp : vm_init_sp (m_vmmaps model') = vm_init_sp (m_vmmaps model) }.
Definition slice_mem (s : slarm) (addr n : word) (FULL FULL' : word -> option byte) : Prop :=
(forall x : word, bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= bv_unsigned x -> FULL' x = FULL x)
/\ (forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + bv_unsigned n ->
FULL' x = if sl_nn s then None else Some (Z_to_bv 8 0)).
Record slice_hyps (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model)
(s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte) : Prop := SH_ {
sh_C : CSOK E cs R FULL model;
sh_m : In m (a_maps cs);
sh_nf : is_fog m = false;
sh_Un : bv_unsigned n = nZ;
sh_pos : 0 < nZ;
sh_nal : nZ mod 4096 = 0;
sh_al : bv_unsigned addr mod 4096 = 0;
sh_in1 : bv_unsigned (edenot E (am_base m)) <= bv_unsigned addr;
sh_in2 : bv_unsigned addr + nZ <= bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m));
sh_post : slice_post s addr n model model';
sh_mem : slice_mem s addr n FULL FULL';
sh_F : s = SlF -> am_kind m = KRWLAZY;
sh_nF : s <> SlF -> am_kind m <> KRWLAZY }.
Section Slice.
Variables (E : env) (cs : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Variables (s : slarm) (m : amap) (addr n : word) (nZ : Z) (model' : Model) (FULL' : word -> option byte).
Hypothesis SH : slice_hyps E cs R FULL model s m addr n nZ model' FULL'.
Let HC := sh_C _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Hm := sh_m _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Hnf := sh_nf _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Un := sh_Un _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let HnZpos := sh_pos _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let HnZal := sh_nal _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Hal := sh_al _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Hin1 := sh_in1 _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let Hin2 := sh_in2 _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let SPo := sh_post _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let SM := sh_mem _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let HF := sh_F _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let HnF := sh_nF _ _ _ _ _ _ _ _ _ _ _ _ SH.
Let lo := bv_unsigned addr.
Let hi := bv_unsigned addr + nZ.
Lemma sl_bounds : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q<'I&YCz&\6yR0&WMvQ5&U>v[0%211%5241%8271%;2:1'J'Q4&YE&U<%119%=2<1%@2?1+TP0%6221%9381D%82<3%;3:1F'N&YA&Y>%129A&UOv0%211%6241&UN%114%921@%;241&WD%11Q0%=2;1%Q8241%Q92A1%Q:2D1%Q;2O1").
Proof.
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as B.
exact (proj1 (Forall_forall _ _) B (amap_den E m) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)).
Qed.
Lemma sl_lohi : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q6'I'N&YAvZD&UOv0%211%5241&UN%114vZO%9221%;251&WDvQ5%211%>2=1&YC%128?&YH+2+R0%3221%E2D1'J'Q4&YE+TP0%22B1z%63521%52L4%83713%Q1231%Q22;1%Q32A1%Q42D1%Q52I1").
Proof.
pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5). pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT. subst lo hi. unfold TOPC in *.
repeat split; try lia. rewrite Z.add_mod, Hal, HnZal by lia. reflexivity.
Qed.
Lemma sl_in_maps : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "M'\5yR0%211'I&YAvZO&\6r1%2271%5241&YCvZD%2241%:241'J'8&W=r2%<2A1&RL&R?v[5%211%411%8261(F%<3;21p0>1phLJ1").
Proof.
intros x Hx. eapply in_ivs_maps_match; [exact (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hm | exact Hnf |]. subst lo hi. lia.
Qed.
Lemma sl_wf' : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "3&XFv[6%211").
Proof.
pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & Wsp). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
assert (iv_wf (addr, n)) by (unfold iv_wf, B, S; cbn; subst lo hi; lia).
unfold model_ivs_wf. rewrite (sp_maps _ _ _ _ _ SPo), (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo).
split; [exact W1|]. split; [|split; [|unfold init_sp_ok in *; rewrite (sp_isp _ _ _ _ _ SPo); exact Wsp]].
- apply ivs_wf_app; [destruct (sl_nn s); [apply ivs_wf_cons; [assumption | apply ivs_wf_nil] | apply ivs_wf_nil] |].
apply maps_subtract_wf; [exact W2 | rewrite Un; lia].
- destruct s; try exact W3; try (apply ivs_wf_cons; [assumption|]); apply maps_subtract_wf; try assumption; rewrite Un; lia.
Qed.
Lemma sl_noacc_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q0'\5yR0%211'N&YC&\6r1%2261vZO%5221&YAvZD%2215%:241'J'8&W=r2%=2A1&RM&R?v[6%211%411%8261v[5%611%811%<2:1%?3>51p0A1phLM1").
Proof.
intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite !in_ivs_covered.
rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with false
by (symmetry; unfold in_rng; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
destruct (sl_nn s); cbn [app]; [|rewrite andb_true_r; reflexivity].
rewrite <- in_ivs_covered, in_ivs_cons. cbn [fst snd in_ivs existsb]. rewrite Un.
replace ((bv_unsigned addr <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned addr + nZ))%bool with false
by (symmetry; apply andb_false_iff; subst lo hi; destruct Hx; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
cbn [orb]. rewrite andb_true_r. reflexivity.
Qed.
Lemma sl_noacc_in : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "O'\5yR0%211'I&YAvZO&\6r1%2271%5241&YCvZD%2241%:241'J'8&W=r2%<2A1&RM&R?v[6%211%411%8261&T=v[N%211%>3=41p0@1phLL1").
Proof.
intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _).
rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app. rewrite (in_ivs_covered _ (maps_subtract _ _ _)).
rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un.
replace (in_rng (bv_unsigned addr) (bv_unsigned addr + nZ) (bv_unsigned x)) with true
by (symmetry; unfold in_rng; apply andb_true_intro; subst lo hi; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
cbn [negb]. rewrite andb_false_r, orb_false_r.
destruct (sl_nn s); cbn [app in_ivs existsb fst snd]; [|reflexivity]. rewrite Un.
rewrite (proj2 (Z.leb_le _ _)) by (subst lo; lia). rewrite (proj2 (Z.ltb_lt _ _)) by (subst hi; lia). reflexivity.
Qed.
Lemma sl_lazy_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "N'\5yR0%211'N&YC&\6r1%2261vZO%5221&YAvZD%2215%:241'J'8&RD&RCr2%211&R=v[6%211%7241v[5%511%:271%=3<41p0?1phLK1").
Proof.
intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
pose proof (page_of_byte_out_aligned x lo hi L5 L6 Hx) as P. subst lo hi.
rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
- apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
- rewrite page_in_ranges_cons_out; [| unfold page_size; rewrite Un; lia | rewrite Un; lia].
apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
- apply page_in_ranges_subtract_out; [exact W3 | rewrite Un; lia | unfold page_size; rewrite Un; lia].
Qed.
Lemma sl_lazy_in : forall x : word, lo <= bv_unsigned x < hi ->
page_in_ranges (page_base x) (m_vm_lazy model') =
match s with SlM => page_in_ranges (page_base x) (m_vm_lazy model) | SlF => true | _ => false end.
Proof.
intros x Hx. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
destruct (page_of_byte_in_aligned x lo hi L5 L6 Hx) as [P1 P2]. subst lo hi.
rewrite (sp_lazy _ _ _ _ _ SPo). destruct s; try reflexivity.
- apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
- apply page_in_ranges_cons_in; unfold page_size; rewrite ?Un; lia.
- apply page_in_ranges_subtract_in; [exact W3 | rewrite Un; lia].
Qed.
Lemma sl_vis_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q9'U:'\5yR0%211'J'='D'X0%2211%411&U8r2%211vZ6%411%;3631'N&YC&\6%12A8vZO%4221&YAvZD%2215%9241'8&WEv0vQ5r4v[6r3%6554321v[5%8576F13%Q03:31p0<1p0G1phLQ41pdBQ81").
Proof.
intros cs1 x Hv Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_noacc_out x Hx), (sl_lazy_out x Hx), (in_allow_ext E cs cs1 Hv). reflexivity.
Qed.
Lemma sl_MR_out : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q?'U:'\5yR0%211'J'='D'X0%2211%411&U8r2%211vZ6%411%;3631'N&YC&\6%12A8vZO%4221&YAvZD%2215%9241'Ay8%K11%311&W6v0vZ0vQ5r4v[6vQ<r3%877654321v[5vQ;%;7:98L214%Q63=41p0B1p0M1phLQ:1pdBQ>1").
Proof.
intros cs1 x Hv Hx. unfold Mr, mrestrict, hid. rewrite (sl_vis_out cs1 x Hv Hx). rewrite (proj1 SM x) by (subst lo hi; rewrite Un; exact Hx). reflexivity.
Qed.
Lemma sl_vis_in_E : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q2'J'T>v[N(SN%43321'U:'\5yR0%211'I&YAvZO&\6r1%2271%5241&YCvZD%2241%:241'8&WEv0vQ5r3v[6r2%6554321(F%M3921p0;1phLG1pdBK1p0M1").
Proof.
intros Hs cs1 x Hx. unfold vis. rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx). subst s.
cbn. rewrite !orb_true_r. reflexivity.
Qed.
Lemma sl_vis_in_G : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q7'J'T>v[N(T0%43321'U:'\5yR0%211'I&YAvZO&\6r1%2271%5241&YCvZD%2241%:241'8vZ0vQ5r2%3221(:%J3621&WEv0r4v[6r3%554:321%Q13=18p081p0@1phLL1pdBQ01p0Q21").
Proof.
intros Hs cs1 x Hx Ha. pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). unfold vis.
rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx). subst s. cbn [sl_nn negb andb].
replace (in_hull A (bv_unsigned x)) with false by (symmetry; unfold in_hull; apply andb_false_iff; destruct L1; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia).
replace (utop E <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
Qed.
Lemma sl_vis_in_F : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "Q>'J'T>v[N(SO%43321'U:'\5yR0%211'='D'X0%2211%411&U8r2%211vZ6%411%C3631'I&YAvZO&\6%12A9%4231&YCvZD%2241%9241'8&WEv0vQ5r4v[6r3%6554321v[5%8576F13%Q83:31p0<1p0G1phLQ31pdBQ71p0Q91").
Proof.
intros Hs cs1 x Hv Hx. unfold vis.
rewrite (sp_maps _ _ _ _ _ SPo), (sl_in_maps x Hx), (sl_noacc_in x Hx), (sl_lazy_in x Hx), (in_allow_ext E cs cs1 Hv).
destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm (HF Hs) x ltac:(subst lo hi; lia)) as [K1 K2].
rewrite K1, K2. subst s. reflexivity.
Qed.
Lemma sl_eager : eager_used model' <= eager_used model + (if sl_charge s then nZ else 0).
Proof.
pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _). pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6).
rewrite (eager_used_sem model' sl_wf'), (eager_used_sem model Hwf). rewrite (sp_maps _ _ _ _ _ SPo).
set (C := vm_noaccess (m_vmmaps model) ++ m_vm_lazy model).
set (C' := vm_noaccess (m_vmmaps model') ++ m_vm_lazy model').
assert (CEQ : forall x, covered C' x =
((sl_nn s && in_rng lo hi x)
|| (covered (vm_noaccess (m_vmmaps model)) x && negb (in_rng lo hi x))
|| match s with
| SlM => covered (m_vm_lazy model) x
| SlF => in_rng lo hi x || (covered (m_vm_lazy model) x && negb (in_rng lo hi x))
| _ => covered (m_vm_lazy model) x && negb (in_rng lo hi x)
end)%bool).
{ intros x. subst C'. rewrite (sp_noacc _ _ _ _ _ SPo), (sp_lazy _ _ _ _ _ SPo). rewrite !covered_app.
rewrite covered_maps_subtract by (try exact W2; rewrite Un; lia). rewrite Un. fold hi. fold lo.
assert (HD : covered (if sl_nn s then [(addr, n)] else []) x = (sl_nn s && in_rng lo hi x)%bool).
{ destruct (sl_nn s); cbn [covered existsb]; [|reflexivity]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. fold lo hi. apply orb_false_r. }
rewrite HD. f_equal.
assert (SC : lo <= hi) by (unfold lo, hi; lia).
destruct s; cbn [sl_nn]; rewrite ?covered_maps_subtract by first [exact W3 | exact SC]; try reflexivity.
unfold covered at 1. cbn [existsb]. fold (covered (maps_subtract (m_vm_lazy model) lo hi) x).
rewrite covered_maps_subtract by first [exact W3 | exact SC]. unfold in_iv, B, S. cbn [fst snd]. rewrite Un. reflexivity. }
assert (CC : forall x, covered C x = (covered (vm_noaccess (m_vmmaps model)) x || covered (m_vm_lazy model) x)%bool).
{ intros x. subst C. apply covered_app. }
assert (MONO : sum_count (fun x => negb (covered C' x)) (vm_maps (m_vmmaps model))
<= sum_count (fun x => (negb (covered C x) || (in_rng lo hi x && sl_charge s))%bool) (vm_maps (m_vmmaps model))).
{ apply sum_count_mono. intros x Hx. apply negb_true_iff in Hx. rewrite CEQ in Hx. rewrite CC.
destruct s; cbn [sl_nn sl_charge] in Hx |- *;
destruct (in_rng lo hi x), (covered (vm_noaccess (m_vmmaps model)) x), (covered (m_vm_lazy model) x); cbn in Hx |- *; congruence. }
pose proof (sum_count_or_le (fun x => negb (covered C x)) (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model))) as OR.
assert (CH : sum_count (fun x => (in_rng lo hi x && sl_charge s)%bool) (vm_maps (m_vmmaps model)) <= (if sl_charge s then nZ else 0)).
{ destruct (sl_charge s).
- rewrite (sum_count_ext _ (in_rng lo hi)) by (intros; apply andb_true_r).
pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) lo hi
(co_seps _ _ _ _ _ _ _ _ _ _ _ HC) (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf)
ltac:(unfold lo; lia) ltac:(unfold hi; lia) ltac:(unfold lo, hi; lia)) as OV.
unfold overlap_sum in OV. unfold lo, hi in *. lia.
- rewrite (sum_count_ext _ (fun _ => false)) by (intros; apply andb_false_r).
clear. induction (vm_maps (m_vmmaps model)) as [|q l IH]; cbn; [lia|]. unfold iv_count. rewrite zcount_const_false. lia. }
cbv beta in OR. lia.
Qed.
Lemma page_base_aligned : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "C'\5yR0%211'J'Q4&YE&\6r1%2271+TP0%5221z%93821&RCr2%211%=3>12p051pg:@1").
Proof.
intros p Hp. unfold page_base, page_base_of, page_size. apply bv_eq. pose proof (u64_range p).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
rewrite u64_lit; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.
Definition sl_hna (ae ne : expr) : list hop := (if sl_nn s then [HCons ae ne] else []) ++ HSub ae ne :: a_hna cs.
Definition sl_hlz (ae ne : expr) : list hop :=
match s with SlM => a_hlz cs | SlF => HCons ae ne :: HSub ae ne :: a_hlz cs | _ => HSub ae ne :: a_hlz cs end.
Lemma slice_cs1_ok : forall sr' R' k' p nx nhi (ae ne : expr),
regs_ok E sr' R' ->
know_ok SEGS E (MR E cs model' FULL') k' ->
nZ <= nhi ->
(sl_charge s = true -> a_eager cs + a_abytes cs + nhi <= LIMIT) ->
edenot E ae = addr -> edenot E ne = n ->
CSOK E (ACS (mk_ss p sr' k' nx)
(match s with SlF => a_maps cs | _ => rekind (a_maps cs) m end)
(a_totsz cs) (a_ylo cs)
(if sl_charge s then a_eager cs + nhi else a_eager cs)
(a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (sl_hna ae ne) (sl_hlz ae ne)) R' FULL' model'.
Proof.
intros sr' R' k' p nx nhi ae ne Hregs Hknow Hnhi Hbudget Hae HneX.
assert (Es : exists s0, s0 = s) by (exists s; reflexivity). destruct Es as [s0 Es].
pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf. pose proof Hwf as (W1 & W2 & W3 & _).
pose proof sl_lohi as (L1 & L2 & L3 & L4 & L5 & L6). pose proof sl_bounds as (B1 & B2 & B3 & B4 & B5).
pose proof sl_wf' as Hwf'. pose proof sl_eager as EG.
pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SEPS. pose proof (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) as MM.
assert (DISJ := fun m' Hm' Hnf' Hne => maps_match_disjoint E (a_maps cs) _ m m' MM SEPS Hm Hm' Hnf Hnf' Hne).
assert (DISJ' : forall m', In m' (a_maps cs) -> is_fog m' = false -> m <> m' ->
bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) <= lo
\/ hi <= bv_unsigned (edenot E (am_base m'))).
{ intros m' Hm' Hnf' Hne. pose proof (DISJ m' Hm' Hnf' Hne) as D. unfold iv_disjoint, amap_den in D. cbn [fst snd] in D. unfold lo, hi. lia. }
assert (KNF : forall m', am_kind m' = KNONE \/ am_kind m' = KNONELAZY \/ am_kind m' = KRWLAZY -> is_fog m' = false).
{ intros m' Hk. unfold is_fog. destruct Hk as [-> |[-> | ->]]; reflexivity. }
assert (NONE : forall m', In m' (a_maps cs) -> m <> m' -> (am_kind m' = KNONE \/ am_kind m' = KNONELAZY) ->
In (amap_den E m') (vm_noaccess (m_vmmaps model'))).
{ intros m' Hm' Hne Hk. rewrite (sp_noacc _ _ _ _ _ SPo). apply in_app_iff. right.
assert (Hnf' : is_fog m' = false) by (apply KNF; tauto).
pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk) as X.
pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) (amap_den E m')
(maps_match_In E _ _ m' MM Hm' Hnf')) as (Bm1 & _).
unfold amap_den in *. apply maps_subtract_keeps; [rewrite Un; lia | exact Bm1 | exact X |].
cbn [fst snd]. rewrite Un. pose proof (DISJ' m' Hm' Hnf' Hne). unfold lo, hi in *. lia. }
assert (KINDS : forall m', In m' (a_maps cs) -> am_kind m' = KRWLAZY ->
forall x : word, bv_unsigned (edenot E (am_base m')) <= bv_unsigned x < bv_unsigned (edenot E (am_base m')) + bv_unsigned (edenot E (am_len m')) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model')) = false
/\ page_in_ranges (page_base x) (m_vm_lazy model') = true).
{ intros m' Hm' Hk x Hx.
destruct (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m' Hm' Hk x Hx) as [K1 K2].
destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
- rewrite sl_noacc_out, sl_lazy_out by lia. auto.
-
assert (Hmm : m = m').
{ destruct (amap_eqb m m') eqn:He; [apply APSK.amap_eqb_eq in He; exact He|]. exfalso.
assert (Hne : m <> m') by (intros ->; rewrite amap_eqb_refl in He; discriminate).
pose proof (DISJ' m' Hm' ltac:(apply KNF; tauto) Hne). lia. }
subst m'. rewrite sl_noacc_in, sl_lazy_in by lia.
destruct s0; rewrite <- Es; cbn [sl_nn]; auto; exfalso; refine (HnF _ Hk); rewrite <- Es; discriminate.
- rewrite sl_noacc_out, sl_lazy_out by lia. auto. }
match goal with |- CSOK _ ?c _ _ _ => set (cs1 := c) end.
assert (HIDOUT : forall x : word, bv_unsigned x < lo \/ hi <= bv_unsigned x -> HID E cs1 model' x = HID E cs model x).
{ intros x Hx. unfold hid. rewrite (sl_vis_out cs1 x eq_refl Hx). reflexivity. }
assert (HALLOW : ALLOW E cs1 = ALLOW E cs) by reflexivity.
destruct HC as [Xregs Xlog Xknow Xhalt Xfds Xfs Xtid Xres Xlimit Xmaps Xholes Xseps Xwf Xbounds Xlazyb Xnasub Xnone Xkinds Xtotsz Xisp Xbrk Xsbrk Xeager Xabytes Xminv Xzero Xsinv Xhna Xhlz Xtidv].
constructor; rewrite ?HALLOW; unfold cs1; cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset a_hna a_hlz kn s_regs s_log s_know s_next mk_ss]; fold cs1.
- exact Hregs.
- reflexivity.
- unfold Mr. rewrite (hid_ext A argH E cs _ model') by reflexivity. exact Hknow.
- rewrite (sp_halted _ _ _ _ _ SPo). exact Xhalt.
- unfold fds_ok in *. rewrite (sp_fds _ _ _ _ _ SPo), (sp_fs _ _ _ _ _ SPo). exact Xfds.
- rewrite (sp_fs _ _ _ _ _ SPo). exact Xfs.
- rewrite (sp_tid _ _ _ _ _ SPo). exact Xtid.
- rewrite (sp_res _ _ _ _ _ SPo). exact Xres.
- rewrite (sp_limit _ _ _ _ _ SPo). exact Xlimit.
- rewrite (sp_maps _ _ _ _ _ SPo).
assert (RK : maps_match E (rekind (a_maps cs) m) (vm_maps (m_vmmaps model))).
{ unfold rekind. apply maps_match_rekind; [|exact Xmaps]. intros m0. destruct (amap_eqb m0 m) eqn:He; [|auto].
apply APSK.amap_eqb_eq in He. subst m0. cbn [am_base am_len]. split; [reflexivity|]. split; [reflexivity|]. rewrite Hnf. reflexivity. }
destruct s0; rewrite <- Es; first [exact RK | exact Xmaps].
-
rewrite (sp_maps _ _ _ _ _ SPo), (sp_res _ _ _ _ _ SPo).
assert (RKH : Forall (hole_ok E (a_ylo cs) (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model))) (rekind (a_maps cs) m)).
{ unfold rekind. apply Forall_forall. intros m0 HinR Hh. apply in_map_iff in HinR as (m1 & <- & HinR1).
destruct (amap_eqb m1 m) eqn:He.
- exfalso. unfold is_hole in Hh. cbn [am_kind] in Hh. discriminate.
- exact (proj1 (Forall_forall _ _) Xholes m1 HinR1 Hh). }
destruct s0; rewrite <- Es; first [exact RKH | exact Xholes].
- rewrite (sp_maps _ _ _ _ _ SPo). exact Xseps.
- exact Hwf'.
- rewrite (sp_maps _ _ _ _ _ SPo). exact Xbounds.
- rewrite (sp_lazy _ _ _ _ _ SPo).
assert (SUB : Forall (fun iv : word * word => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
/\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E)
(maps_subtract (m_vm_lazy model) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))).
{ apply Forall_forall. intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3 Hq) as (r & Hr & R1 & R2 & _).
pose proof (proj1 (Forall_forall _ _) Xlazyb r Hr) as [Y1 Y2]. lia. }
destruct s0; rewrite <- Es; try exact SUB; try exact Xlazyb. apply Forall_cons; [cbn [fst snd]; unfold lo, hi in *; lia | exact SUB].
- intros z Hz. rewrite (sp_maps _ _ _ _ _ SPo). rewrite (sp_noacc _ _ _ _ _ SPo), in_ivs_app in Hz.
apply orb_prop in Hz as [Hz|Hz].
+ destruct (sl_nn s); [|discriminate]. rewrite in_ivs_cons in Hz. cbn [fst snd in_ivs existsb] in Hz. rewrite orb_false_r in Hz.
apply andb_prop in Hz as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
eapply in_ivs_maps_match; [exact Xmaps | exact Hm | exact Hnf |]. unfold lo, hi in *. lia.
+ apply Xnasub. rewrite in_ivs_covered in Hz |- *. rewrite covered_maps_subtract in Hz by (try exact W2; rewrite Un; lia).
apply andb_prop in Hz as [Hz _]. exact Hz.
- apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
2: { apply NONE; [exact Hm' | | exact Hk']. intros <-. rewrite (HF (eq_sym Es)) in Hk'. destruct Hk'; discriminate. }
all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; destruct Hk'; discriminate|];
apply NONE; [exact Hm0 | congruence | exact Hk'].
- apply Forall_forall. intros m' Hm' Hk'. destruct s0; rewrite <- Es in Hm'.
2: { apply KINDS; assumption. }
all: destruct (in_rekind _ _ _ Hm') as (m0 & Hm0 & [[-> ->]|[Hne ->]]); [cbn in Hk'; discriminate|];
apply KINDS; assumption.
- rewrite (sp_res _ _ _ _ _ SPo), (sp_maps _ _ _ _ _ SPo). exact Xtotsz.
- rewrite (sp_isp _ _ _ _ _ SPo). exact Xisp.
- rewrite (sp_brk _ _ _ _ _ SPo). exact Xbrk.
- rewrite (sp_brk _ _ _ _ _ SPo), (sp_sbrk _ _ _ _ _ SPo). exact Xsbrk.
- destruct (sl_charge s); lia.
- exact Xabytes.
- destruct Xminv as [N1 N2 N3 N4 N5].
assert (MAT : forall q, In q (m_vm_materialized model') -> In q (m_vm_materialized model)
/\ (s <> SlM -> bv_unsigned q < lo \/ hi <= bv_unsigned q)).
{ intros q Hq. pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT in Hq; try (split; [exact Hq | congruence]).
all: apply filter_In in Hq as [Hq Ho]; split; [exact Hq|]; intros _;
unfold page_outside_range in Ho; apply negb_true_iff in Ho; apply andb_false_iff in Ho as [Ho|Ho];
[apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold lo, hi; rewrite <- ?Un; lia. }
constructor; rewrite ?(sp_limit _ _ _ _ _ SPo).
+ pose proof (sp_mat _ _ _ _ _ SPo) as SMAT. destruct s0; rewrite <- Es in SMAT; rewrite SMAT; try apply NoDup_filter; exact N1.
+ intros q Hq. apply N2. apply MAT. exact Hq.
+ intros q Hq. apply N3. apply MAT. exact Hq.
+ intros q Hq. destruct (MAT q Hq) as [Hq0 Hout]. pose proof (N4 q Hq0) as L0.
pose proof (sl_lazy_out q) as LO. pose proof (sp_lazy _ _ _ _ _ SPo) as SL.
destruct s0; rewrite <- Es in SL, Hout; [| | | rewrite SL; exact L0].
all: specialize (Hout ltac:(discriminate)); rewrite <- (page_base_aligned q (N2 q Hq0)); rewrite LO by exact Hout;
rewrite page_base_aligned by exact (N2 q Hq0); exact L0.
+ destruct (sl_charge s); [specialize (Hbudget eq_refl)|]; rewrite Xlimit in *; lia.
- intros x Hh Hmx Hna Hlz Hgh.
destruct (Z_lt_le_dec (bv_unsigned x) lo) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned x) hi) as [Hlt2|Hge2]].
+ rewrite (proj1 SM x) by (unfold lo in *; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
+ rewrite sl_noacc_in in Hna by lia. rewrite (proj2 SM x) by (unfold lo, hi in *; rewrite Un; lia). rewrite Hna. reflexivity.
+ rewrite (proj1 SM x) by (unfold hi in *; rewrite Un; lia). rewrite HIDOUT in Hh by lia. rewrite (sp_maps _ _ _ _ _ SPo) in Hmx.
rewrite sl_noacc_out in Hna by lia. rewrite sl_lazy_out in Hlz by lia. exact (Xzero x Hh Hmx Hna Hlz Hgh).
- eapply SINV_frame; [|exact Xsinv]. intros x Hx. apply (proj1 SM). pose proof (argH_high _ _ Hx). pose proof (utop_bounds E). unfold hi in *. rewrite Un. lia.
- rewrite (sp_noacc _ _ _ _ _ SPo), Xhna. unfold sl_hna, RNA.
destruct s0; rewrite <- Es; cbn [sl_nn app hreplay]; unfold APSK.uE; rewrite Hae, HneX; reflexivity.
- rewrite (sp_lazy _ _ _ _ _ SPo), Xhlz. unfold sl_hlz, RLZ.
destruct s0; rewrite <- Es; cbn [hreplay]; unfold APSK.uE; rewrite ?Hae, ?HneX; reflexivity.
- intros Ht. rewrite (sp_tid _ _ _ _ _ SPo). exact (Xtidv Ht).
Qed.
End Slice.
Lemma kn_unfill_clip_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "R='WN'\5yR0%211'Ay8%511%311p051phL62'='X2%211'X0'Q4&X=vY8r7r6r4%544321'N&YA&Y>&X;r8(WKr3%2291%5241&X:r2%2271%:241&UOv0%211%?241&UN%114%B21;%D241&YC&\6r1%22Q;1r:r5%F2N1%I231%8251%E25Q0%M231%O218%Q1241'Jr9%11J%<1K%43QD21p061phLQJ1&V7&V;%14Q?Q>AQ=%32N1%QC4QBDQ91p061p0K1p0QA1pfLQI1pg8QI1pd4QK1pe@QM1pW4R11pW2R31pR<R<1").
Proof.
intros E M M' k b off ne HK Hhull Hout.
pose proof (kimg_clip_in_hull' (kn_unfill k b off ne)) as Hh.
unfold know_ok. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
apply kimg_clip_incl in Hin. unfold kn_unfill in Hin. apply filter_In in Hin as [Hin Hkeep].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
eapply kentry_keep_sem'; [exact HKK | | exact Hout].
apply orb_prop in Hkeep as [Himg|Hap].
- destruct K; try discriminate. unfold kfoot_apart, kfoot. cbn in HKh. lia.
- rewrite APSK.kentry_apart_bp_eq in Hap. eapply kentry_apart_b_sem'; [exact HK | exact Hap].
Qed.
Lemma kn_rezero_ok_gen : forall E M M' k b off ne,
know_ok SEGS E M k ->
(estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)) ->
(forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x -> M' x = M x) ->
(forall x : word, estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E ne -> M x <> None -> M' x = Some (Z_to_bv 8 0)) ->
forall K, In K (kn_rezero k b off ne) ->
match K with KImg lo hi => img_lo A <= lo /\ hi <= img_hi A | _ => True end ->
kentry_ok SEGS E M' K.
Proof.
intros E M M' k b off ne HK Hhull Hout Hin0 K Hin HKh.
assert (DEF : forall x : word, M x <> None -> M' x <> None).
{ intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [rewrite (Hin0 x ltac:(lia) Hx); discriminate | rewrite Hout by lia; exact Hx]. }
assert (ZERO : forall x : word, M x = Some (Z_to_bv 8 0) -> M' x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off))); [rewrite Hout by lia; exact Hx|].
destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA b off) + elenZ E ne)); [apply Hin0; [lia | rewrite Hx; discriminate] | rewrite Hout by lia; exact Hx]. }
unfold kn_rezero in Hin. apply filter_In in Hin as [Hin Hkeep].
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct K as [[kb kk] w v|[kb kk] l|[kb kk] l bk|ilo ihi|e mm|e rlo rhi|[kb kk] l|a1 n1 a2 n2|[kb kk] l fc|[kb kk] l];
try (rewrite APSK.kentry_apart_bp_eq in Hkeep; eapply kentry_keep_sem'; [exact HKK | eapply kentry_apart_b_sem'; [exact HK | exact Hkeep] | exact Hout]).
- cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply ZERO. apply Hz. exact Hi.
- eapply kentry_keep_sem'; [exact HKK | | exact Hout]. unfold kfoot_apart, kfoot. lia.
- exact HKK.
- exact HKK.
- cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hs]. split; [exact Hfl|]. intros d mm Hd Hdm. eapply store_ok_mono; [exact DEF | apply Hs; assumption].
- exact HKK.
- cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. apply DEF. apply Hz. exact Hi.
Qed.
Lemma kn_rezero_clip_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "S7'WN'\5yR0%211'Ay8%511%311p051phL62'='X2%211'X0'Q4&X=vY8r7r6r4%544321'N&YA&Y>&X;r8(WKr3%2291%5241&X:r2%2271%:241&UOv0%211%?241&UN%114%B21;%D241&YC&\6r1%22Q;1r:r5%F2N1%I231%8251%E25Q0%M231%O218%Q1241'Jr9%11J%<1K%43QD21p061phLQJ1'Ir;%Q62Q?Q>%Q9221%Q<21E%Q524D%Q=231%K2H1%8241&M%91Q9(3%11R4%D3R431%511%>1QB(5&\4z%22R<1%42R<1%L3R<61p081p0?1phLRC1&V7&V:%14R0R8R7Q:%32QG1%R<4R;LQ31p061p0Q01p0QE1p0R;1pfLRC1pg8RC1pd4RE1pe@RG1pW4RK1pW2RM1pR<S61").
Proof.
intros E M M' k b off ne HK Hhull Hout Hin0. pose proof (kimg_clip_in_hull' (kn_rezero k b off ne)) as Hh.
unfold know_ok. apply Forall_forall. intros K Hin. pose proof (proj1 (Forall_forall _ _) Hh K Hin) as HKh.
apply kimg_clip_incl in Hin. apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.
Lemma kn_rezero_hull_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "S9'WN'\5yR0%211'Ay8%511%311p051phL62'='X2%211'X0'Q4&X=vY8r7r6r4%544321&W?v0r5%3221'N&YA&Y>&X;r9(WK%128<%4231&X:r3%2261%9241&UO%11@%=231&UN%11C%@21:%B241&YC&\6r1%22Q=1r;%C2Q0O%F221%7241%C24M%J231%L217%N241'Jr:r2%211%<12%53QF21p071phLQL1'Ir<r8%Q521QB%Q8231%Q;21F%Q525QD%Q<231%L2I1%9241&M%:1A(3%11R7%F3R731%511%?1Q>(5&\4z%22R?1%42R?1%N3R?61p081p0?1phLRF1&V:%14QNIR:R9%R=4R<KQ31p041p0O1p0QD1p0R81p0R=1pfLRE1pg8RE1pd4RG1pe@RI1pW4RM1pW2RO1pR<S81").
Proof.
intros E M M' k b off ne HK Hh Hhull Hout Hin0.
unfold know_ok. apply Forall_forall. intros K Hin.
assert (Hin' : In K k) by (unfold kn_rezero in Hin; apply filter_In in Hin as [Hin _]; exact Hin).
pose proof (proj1 (Forall_forall _ _) Hh K Hin') as HKh.
apply (kn_rezero_ok_gen E M M' k b off ne HK Hhull Hout Hin0 K Hin). destruct K; try exact I. exact HKh.
Qed.
Lemma kimg_in_hull_cons2 : forall K1 K2 k,
match K1 with KImg _ _ => False | _ => True end -> match K2 with KImg _ _ => False | _ => True end ->
kimg_in_hull A k -> kimg_in_hull A (K1 :: K2 :: k).
Proof.
intros K1 K2 k H1 H2 Hk. unfold kimg_in_hull in *. constructor; [destruct K1; tauto|]. constructor; [destruct K2; tauto | exact Hk].
Qed.
Lemma vis_add_slice_ok : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "T>'WN'U:'X0'Q4&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'W9vY8v0vQ?vY9vZ0vQ:r<r;r5r4r3%<;;:987654321'J%D1M&W1r:r7(9'X2(WI(WKr9r8%3221%5218(WJ%123:&V8%11F%<3;31%=3<61%A6NMI@?1(5%12QAJ%F3E31&W?r=%:11%32Q51&WCr?%221Q3%N3QH1Q2&X;r@%I2Q7Q6%3221r6%Q43QN21&X:rA%221Q<%Q83R215&YAz%221Q1&YC%123Q3&Y>%12Q<Q6&TL%8221'I&\6r1%22R;1%=2QL1%92QMQL%<231%7231'8&W=r2%:2RC1&RL&R?r>%211%411%8261(F%R53;21&RM%116%=2;1(:%R:3@21rG%RD21@%R=3C14%QB1B&\4%12S2Q6%QM2S21%RB3S241%Q1261%Q22:1%Q32@1p0M1phLS<1rFrD%S7;S6S5S4S3S2S121QNJR2p041p0Q;1p0Q@1p0QC1p0QG1p0QL1p0R31p0R81p0R=1p0S51pfHSO1pf0T01pf>SE1pRJSG1pW:SM1pfLT51pg8T51pd4T71pdHT81pdDT:1pdBT;1pR<T=1").
Proof.
intros E cs1 cs2 ea b off ne R FULL' model' lo nZ HC1 Hva Hkh Hea Hest Hne Hlo HnZ Hhi NEW.
eapply vis_add_sound'; [exact Hva | exact HC1 |].
destruct (vis_add_inv cs1 ea ne _ cs2 Hva) as (nhi & Hnhi & Ecs2).
assert (BYTE : forall x : word, lo <= bv_unsigned x < lo + nZ -> MR E cs2 model' FULL' x = Some (Z_to_bv 8 0)).
{ intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & N4).
unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1, N2. cbn [negb andb].
assert (Hal : in_allow A E cs2 (bv_unsigned x) = true).
{ unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd]. rewrite Hea. unfold uE. fold (elenZ E ne). rewrite Hne.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
rewrite Hal, !orb_true_r. cbn [negb]. exact N4. }
assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat; rewrite Hest, Hne; unfold TOPC in Hhi; lia).
constructor; [|constructor].
- cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
apply store_ok_of_all; [rewrite u64_lit by (unfold TOPC in Hhi; lia); unfold TOPC in Hhi; lia|].
intros x Hx. rewrite u64_lit in Hx by (unfold TOPC in Hhi; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
- cbn [kentry_ok]. split; [exact Hfl|]. rewrite Hest, Hne. intros i Hi. apply BYTE. rewrite u64_lit by (unfold TOPC in Hhi; lia). lia.
- pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
eapply know_ok_unhide'; [apply H_off_segments_cs' | exact Hkh | | | exact HK1].
+ intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
+ intros y Hy. apply hid_hull'. exact Hy.
Qed.
Lemma find_containing_sound : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "RE'WN'\5yR0%211'Ay8%511%311p051'='X2%211'U?%411'V>%611'X0'Q4&X=vY8r9r8r7%544321'J%E1=&UGr6r5r4r3%56:94321(5r2%22F1%;3:41'I&Y:%13J8A&U=%11:%43K1C'8&V3%11>(:%F3421%;261&YA&\6&WMr;&U<%11G%4231%62QE1&X;(WK%12ON%3281%<251&Y>&X:%12<Q2%3251&U>%11Q4%A2@1%C2R21%82>1%F261%Q32;1%Q42I1%Q52Q31p0Q71p0QD1pf2R01pfLQM1pg8QM1pd4QO1peDR11pf@R41pe@R71pW2R;1pR<RD1").
Proof.
intros E M k ms kinds b off ne m HK Hf. unfold find_containing in Hf. apply find_some in Hf as [Hin Hb].
apply andb_prop in Hb as [Hk Hins]. apply andb_prop in Hk as [Hnf Hk]. apply negb_true_iff in Hnf.
apply existsb_exists in Hk as (k0 & Hk0 & Hkk). apply APSK.mkind_eqb_eq in Hkk. subst k0.
pose proof (xinside_sound SEGS E M k b off ne (am_base m) 0 (am_len m) HK Hins) as [I1 I2].
unfold estart in I1, I2 |- *. cbn [a_base a_off] in *. unfold elenZ in *. repeat split; try assumption; lia.
Qed.
Lemma slice_args : ltac2:(TCodec.tc2 tcn__AsanNodesMmLibK "VL'WN'U:&S?y5'\5yR0%211%5241'Ay8%611%311p061'R3'X0'Q4'='V>%211'U?'W9vY8v0vQ?vY9vZ0vQ:r<r;r:r9r8%<;;:987654321'J'D%12ED%221F%321F%421G%O11&UJ&TL%23D?1(5(Cr7%24Q0O?1r6%44=Q221r5%64>Q321r4%84?Q521%:2?1%E3?<1%Q?1Q4&UG&V8r=%211&U4%113%6631;Q0OAr3%E2Q=1%Q03:31&WMr?&VHr>u:%3221%6251&\6r@u;%8291%;231%52R91&REr1%211&\4%12R>3'I&Y:rB%K11%33R5QI1&U=%11QK%63R:1QM'8&V3%11QO(:%QO3421%=261&XNrA&YG%11O%D2S31%5241%R73S21QE%51N%H2S71%9281%J2S7Q=%R<3S721&YCz%221QA&YH+2+R0%3221%72QF1%Q2261rC%QF21RM%RH3SC1Q9%QA2SEQ:r2%RK3S=21%?2>2&YA%124S2&YE+TP0%2271%S23SD1D%QK2SORA%5214%S53SG1G%I2H3'N&Y>%126?&UO%11SF%?231&UN%11SI%B21<%9241&X;(WK%12R?RJ%32N1%SE3T71B&U<%11SI%RG2Q21%RA2TE1%M21G&U>%11SN%RL2Q71%RF2TJ1%G261%Q32G1&WD%11Q<%Q6241&R@&RL&R?%11S5%311%531SGRJ(F%T;3R@21&RG&RN%117%331SMS0%T@3RE16&XG%Q:2Q?QI%23;Q@1%QG21QJ%S2251%S32;1%S42D1%S52H1%S62O1%S72Q51%S82Q;1%S92QF1%S:2QH1%S;2QL1%S<2R11%S=2R41%S>2R61%S?2R:1%S@2R>1%SA2RH1%SB2RN1%SC2S61%SD2S@1tfFV3SF1tfHUKSI1teNULSM1td0V6T41p0T<1p0TH1p0U?1pf2UM1peDUO1pfNV31pg0V41pfLV61pg8V61pd4V81pf<V:1pRHV<1pW:VB1pd>VI1pR<VK1").
Proof.
intros E cs R FULL model b off ne nlo nhi kinds m HC HFA Hf addr len nZ n.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
destruct (fixed_args_sound E cs R FULL model TOPC b off ne nlo nhi HC HFA) as (Hsp & HML & Hal & Hpos & Himg & Htop & R10 & _).
destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & _).
fold addr in Hal, Hpos, Himg, Htop, R10. fold len in R11, Hlen, Hne, HnZ, HnZal. fold nZ in Hne, HnZ, HnZal. fold n in Hne.
destruct (find_containing_sound E _ (kn cs) (a_maps cs) kinds b off ne m HK Hf) as (Hm & [Hkind Hnf] & I1 & I2).
pose proof (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC) as HB.
pose proof (maps_match_In E _ _ m (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) Hm Hnf) as HIN.
pose proof (proj1 (Forall_forall _ _) HB (amap_den E m) HIN) as (B1 & B2 & B3 & B4 & B5). cbn [amap_den fst snd] in B1, B2, B3, B4, B5.
pose proof (u64_range (edenot E (am_base m))) as Rb. pose proof (utop_le_TOPC _ _ _ _ _ HC) as UT.
assert (Hest : bv_unsigned addr = estart E (SA b off)).
{ unfold addr. apply (APSK.u_of_split E (reg cs 10) b off Hsp). unfold elenZ in I2. pose proof (u64_range (edenot E ne)). unfold TOPC in UT. lia. }
unfold elenZ in I2. rewrite Hne in I2.
pose proof (page_round_up_Z_bounds len ltac:(lia)) as PB. fold nZ in PB. unfold page_size in PB.
assert (Un : bv_unsigned n = nZ).
{ unfold n. apply u64_lit. pose proof (u64_range (Z_to_bv 64 nZ)). fold n in H. unfold TOPC in *. lia. }
rewrite Un in I2. rewrite Hne, Un in Himg.
assert (Hmc : map_contains (vm_maps (m_vmmaps model)) addr n = true).
{ eapply map_contains_intro; [exact HIN | lia | rewrite Un; lia]. }
split; [exact Hm|]. split; [split; [exact Hkind | exact Hnf]|].
repeat (split; [first [assumption | lia | symmetry; assumption] |]).
split; [apply reserved_free_hull_apart; [exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Un; exact Himg] |].
rewrite Un. pose proof (overlap_sum_contained (vm_maps (m_vmmaps model)) (edenot E (am_base m)) (edenot E (am_len m)) (bv_unsigned addr) (bv_unsigned addr + nZ)
(co_seps _ _ _ _ _ _ _ _ _ _ _ HC) HIN ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.
End Nodes.
