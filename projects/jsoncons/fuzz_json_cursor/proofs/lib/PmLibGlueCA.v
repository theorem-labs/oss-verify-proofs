(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8IcptLayout Pm8L5DefsA Pm8ArtFsInv Pm8ArtIfaceInst Pm8ArtIfaceInstX PmLibAssemblyCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutRtCpsA.

From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require TopSpecsCA AfterValueCA AnnotateCA AnnotateNullCA AtcCA AtexitHandlerCA BeginArrayCA BeginMemberCA BeginObjectCA ConvertCA DecU64CA DecstrCA DetectCA EndArrayCA EndFractionValueCA EndIntegerValueCA EndNegativeValueCA EndObjectCA EndPositiveValueCA EndStringValueCA ErrHandlerCA GuardCA IssCtorCA LocaleCA LocaleDtorCA OpDelCA OpDelNullCA OpNewCA ParentCA ParseFalseCA ParseNullCA ParseNumberCA ParseStringCA ParseTrueCA ParserDtorCA PopStateCA SetEcCA SkipSpaceCA SourceDtorCA StrAppendCA StrAppendRangeCA StrInitCA StrPushBackCA StrReserveCA SyscatCA TceCA ValidateCA VecDtorCA VecPushCA VecPushSlowCA VecReserveCA XsgetnCA VisitNullCA VisitBoolCA VisitU64CA VisitI64CA VisitDoubleCA VisitKeyCA VisitStringCA VisitBeginObjCA VisitBeginArrCA VisitEndObjCA VisitEndArrCA ParseSomeCA IslCgCA HnKitCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmIslandInstCA Pm8StrtodOk Pm8FloatLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GLC.
Abbreviation IC := PMLA.C_casan.
Abbreviation ASEGS := Asan.M.loaded_segments.

Section Inst.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.

Hypothesis ILok : as0_icpt_layout IL.
Hypothesis ILXok : pm_icpt_layout_x ILX.
Hypothesis HIok : pm_asan_iface_ok art_L art_LX ar art_C scfg HI.
Hypothesis ICok : pm_aicpt_ok art_L ar IL ILX scfg HI (aannotate_spec art_L ar scfg HI (iclx_annotate ILX) 4096).
Hypothesis FN : afree_null_spec art_L ar scfg HI.

Let HIok0 : PmHeapIfaceA.asan_iface_ok art_L ar art_C scfg HI := pio_base _ _ _ _ _ _ HIok.
Let LAY := ASMC.art_lay.
Let FPM := ASMC.art_fpm.
Let FOOTC := ASMC.art_footc.
Lemma FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.
Proof.
  intros a (iv & Hin & Hr). cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro.
  cbn [PMLA.FOOT PMLA.C_casan In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Let ISH : rt_img_shadow art_L IL HI := pic_img_shadow _ _ _ _ _ _ _ ICok.
Lemma ANN : aannotate_spec art_L ar scfg HI 0x82c5c 4096.
Proof. rewrite <- (aiclx_annotate ILX ILXok). exact (pic_annotate _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMSET_LIBC : CRC.amemset_spec_at art_L ar HI 0x7ee68.
Proof.
  rewrite <- (aiclx_memset ILX ILXok).
  intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt).
Qed.
Lemma MEMCPY_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7ee70 false.
Proof. rewrite <- (aicl_memcpy IL ILok). exact (pic_memcpy_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMMOVE_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7ee6c false.
Proof. rewrite <- (aicl_memmove IL ILok). exact (pic_memmove_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMCMP_TU : amemcmp_spec_at art_L ar scfg HI 0x6a564 8192.
Proof. rewrite <- (aiclx_memcmp ILX ILXok), <- (aiclx_scr_memcmp ILX ILXok). exact (pic_memcmp _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF5 : aset_shadow_spec art_L ar scfg HI 0x82aec 245 256.
Proof. rewrite <- (aiclx_setshf5 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf5 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSH00 : aset_shadow_spec art_L ar scfg HI 0x829e4 0 256.
Proof. rewrite <- (aiclx_setsh00 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setsh00 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF8 : aset_shadow_spec art_L ar scfg HI 0x82b04 248 256.
Proof. rewrite <- (aiclx_setshf8 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf8 _ _ _ _ _ _ _ ICok). Qed.

Lemma SF5 : PmHeapIfaceA.astack_free_spec art_L ar scfg HI 0x654c8 0x10398 5.
Proof. rewrite <- ASMC.art_sfree5, <- ASMC.art_sfree_pat. exact (pio_stack_free5 _ _ _ _ _ _ HIok). Qed.
Lemma PATR : 0x10000 <= 0x10398 /\ 0x10398 + 8 <= 0x154000.
Proof. lia. Qed.

Ltac poi := rewrite (aicl_poison IL ILok); unfold ART_POISON; cbv -[Z.le Z.lt Z.add fst snd];
            repeat first [ apply Forall_nil | apply Forall_cons | (cbn [fst snd]; lia) ].

Ltac ilxeq := first [ rewrite (aiclx_cxa_atexit ILX ILXok) | rewrite (aiclx_scr_cxa ILX ILXok) | rewrite (aiclx_atexit_tab ILX ILXok)
                     | rewrite (aiclx_atcxa ILX ILXok) | rewrite (aiclx_need_locks ILX ILXok) ]; first [ reflexivity | lia ].
Ltac client_rng := intros ?a0 ?Ha0; cbn [art_L hl_rt_static hl_rt_ro]; unfold art_static, art_ro;
                   cbv -[Z.le Z.lt Z.ge Z.gt Z.add Z.sub not] in Ha0; lia.
Create HintDb glueA.
Ltac d := first
  [ exact HIok0 | exact LAY | exact FPM | exact FOOTC | exact FOOTC2 | exact ISH | exact ICok | exact FN | exact ANN
  | exact MEMSET_LIBC | exact MEMCPY_LIBC | exact MEMMOVE_LIBC | exact MEMCMP_TU | exact SETSHF5 | exact SETSH00 | exact SETSHF8 | exact SF5 | exact PATR
  | reflexivity
  | solve [auto 2 with glueA]
  | assumption
  | ilxeq
  | poi
  | client_rng ].

Lemma strtod_art : PMSA.strtod_specA art_L ar HI IC 0x1441ac.
Proof. exact (Pm8StrtodOk.STOA.strtod_okA art_L ar art_C HI HIok0 LAY Pm8FloatLayout.art_float). Qed.
#[local] Hint Resolve strtod_art : glueA.

Lemma locale_ctor_first_art : PMSA.locale_ctor_first_specA art_L ar HI IC 0x11a468.
Proof. exact (PmIslandInstCA.ISAI8.locale_ctor_first_art scfg ar HI IL ILX _ ILok ILXok HIok ICok). Qed.
#[local] Hint Resolve locale_ctor_first_art : glueA.
Lemma locale_ctor_first_cg_art : IslCgCA.ICG.locale_ctor_first_specA_cg art_L ar HI IC 0x11a468.
Proof. exact (PmIslandInstCA.ISAI8.locale_ctor_first_art_cg scfg ar HI IL ILX _ ILok ILXok HIok ICok). Qed.
#[local] Hint Resolve locale_ctor_first_cg_art : glueA.

Lemma visit_null_art : PMSA.visit_null_specA art_L ar HI IC 0xcaa2c.
Proof. eapply VisitNullCA.visit_null_ok; d. Qed.
#[local] Hint Resolve visit_null_art : glueA.
Lemma visit_bool_art : PMSA.visit_bool_specA art_L ar HI IC 0xcaad4.
Proof. eapply VisitBoolCA.visit_bool_ok; d. Qed.
#[local] Hint Resolve visit_bool_art : glueA.
Lemma visit_u64_art : PMSA.visit_u64_specA art_L ar HI IC 0xca3e8.
Proof. eapply VisitU64CA.visit_u64_ok; d. Qed.
#[local] Hint Resolve visit_u64_art : glueA.
Lemma visit_i64_art : PMSA.visit_i64_specA art_L ar HI IC 0xca4b8.
Proof. eapply VisitI64CA.visit_i64_ok; d. Qed.
#[local] Hint Resolve visit_i64_art : glueA.
Lemma visit_double_art : PMSA.visit_double_specA art_L ar HI IC 0xca588.
Proof. eapply VisitDoubleCA.visit_double_ok; d. Qed.
#[local] Hint Resolve visit_double_art : glueA.
Lemma visit_key_art : PMSA.visit_key_specA art_L ar HI IC 0xca91c.
Proof. eapply VisitKeyCA.visit_key_ok; d. Qed.
#[local] Hint Resolve visit_key_art : glueA.
Lemma visit_string_art : PMSA.visit_string_specA art_L ar HI IC 0xcabac.
Proof. eapply VisitStringCA.visit_string_ok; d. Qed.
#[local] Hint Resolve visit_string_art : glueA.
Lemma visit_begin_object_art : PMSA.visit_begin_object_specA art_L ar HI IC 0xca65c.
Proof. eapply VisitBeginObjCA.visit_begin_object_ok; d. Qed.
#[local] Hint Resolve visit_begin_object_art : glueA.
Lemma visit_begin_array_art : PMSA.visit_begin_array_specA art_L ar HI IC 0xca874.
Proof. eapply VisitBeginArrCA.visit_begin_array_ok; d. Qed.
#[local] Hint Resolve visit_begin_array_art : glueA.
Lemma visit_end_object_art : PMSA.visit_end_object_specA art_L ar HI IC 0xca7d8.
Proof. eapply VisitEndObjCA.visit_end_object_ok; d. Qed.
#[local] Hint Resolve visit_end_object_art : glueA.
Lemma visit_end_array_art : PMSA.visit_end_array_specA art_L ar HI IC 0xca348.
Proof. eapply VisitEndArrCA.visit_end_array_ok; d. Qed.
#[local] Hint Resolve visit_end_array_art : glueA.

Lemma opnew_art : PMSA.opnew_specA art_L ar HI 1358140.
Proof. eapply OpNewCA.opnew_ok; d. Qed.
#[local] Hint Resolve opnew_art : glueA.
Lemma opdel_art : PMSA.opdel_specA art_L ar HI 975272.
Proof. eapply OpDelCA.opdel_ok; d. Qed.
#[local] Hint Resolve opdel_art : glueA.
Lemma opdel_sized_art : PMSA.opdel_specA art_L ar HI 975276.
Proof. eapply OpDelCA.opdel_sized_ok; d. Qed.
#[local] Hint Resolve opdel_sized_art : glueA.
Lemma opdel_null_art : PMSA.opdel_null_specA art_L ar HI 975272.
Proof. eapply OpDelNullCA.opdel_null_ok; d. Qed.
#[local] Hint Resolve opdel_null_art : glueA.
Lemma guard_acquire_art : PMSA.guard_acquire_specA art_L ar HI 858236.
Proof. eapply GuardCA.guard_acquire_ok; d. Qed.
#[local] Hint Resolve guard_acquire_art : glueA.
Lemma guard_release_art : PMSA.guard_release_specA art_L ar HI 858316.
Proof. eapply GuardCA.guard_release_ok; d. Qed.
#[local] Hint Resolve guard_release_art : glueA.
Lemma annotate_increase_art : PMSA.annotate_increase_spec art_L ar HI 807940.
Proof. eapply AnnotateCA.annotate_increase_ok; d. Qed.
#[local] Hint Resolve annotate_increase_art : glueA.
Lemma annotate_shrink_art : PMSA.annotate_shrink_spec art_L ar HI 726664.
Proof. eapply AnnotateCA.annotate_shrink_ok; d. Qed.
#[local] Hint Resolve annotate_shrink_art : glueA.
Lemma annotate_new_art : PMSA.annotate_new_spec art_L ar HI 808492.
Proof. eapply AnnotateCA.annotate_new_ok; d. Qed.
#[local] Hint Resolve annotate_new_art : glueA.
Lemma annotate_delete_art : PMSA.annotate_delete_spec art_L ar HI 726504.
Proof. eapply AnnotateCA.annotate_delete_ok; d. Qed.
#[local] Hint Resolve annotate_delete_art : glueA.
Lemma annotate_delete_null_art : PMSA.annotate_delete_null_spec art_L ar HI 726504.
Proof. eapply AnnotateNullCA.annotate_delete_null_ok; d. Qed.
#[local] Hint Resolve annotate_delete_null_art : glueA.
Lemma vec_push_slow_art : PMSA.vec_push_slow_spec art_L ar HI 807460.
Proof. eapply VecPushSlowCA.vec_push_slow_ok; d. Qed.
#[local] Hint Resolve vec_push_slow_art : glueA.
Lemma vec_push_art : PMSA.vec_push_specA art_L ar HI 807200.
Proof. eapply VecPushCA.vec_push_ok; d. Qed.
#[local] Hint Resolve vec_push_art : glueA.
Lemma pop_state_art : PMSA.pop_state_specA art_L ar HI 779788.
Proof. eapply PopStateCA.pop_state_ok; d. Qed.
#[local] Hint Resolve pop_state_art : glueA.
Lemma parent_art : PMSA.parent_specA art_L ar HI 800992.
Proof. eapply ParentCA.parent_ok; d. Qed.
#[local] Hint Resolve parent_art : glueA.
Lemma vec_dtor_art : PMSA.vec_dtor_specA art_L ar HI 726216.
Proof. eapply VecDtorCA.vec_dtor_ok; d. Qed.
#[local] Hint Resolve vec_dtor_art : glueA.
Lemma vec_reserve_art : PMSA.vec_reserve_specA art_L ar HI 827068.
Proof. eapply VecReserveCA.vec_reserve_ok; d. Qed.
#[local] Hint Resolve vec_reserve_art : glueA.
Lemma after_value_art : PMSA.after_value_specA art_L ar HI IC 806044.
Proof. eapply AfterValueCA.after_value_ok; d. Qed.
#[local] Hint Resolve after_value_art : glueA.
Lemma begin_member_art : PMSA.begin_member_specA art_L ar HI IC 800308.
Proof. eapply BeginMemberCA.begin_member_ok; d. Qed.
#[local] Hint Resolve begin_member_art : glueA.
Lemma errh_art : PMSA.errh_specA art_L ar HI 822600.
Proof. eapply ErrHandlerCA.errh_ok; d. Qed.
#[local] Hint Resolve errh_art : glueA.
Lemma set_ec_art : PMSA.set_ec_specA art_L ar HI IC 747008.
Proof. eapply SetEcCA.set_ec_ok; d. Qed.
#[local] Hint Resolve set_ec_art : glueA.
Lemma parse_null_art : PMSA.parse_null_specA art_L ar HI IC 793496.
Proof. eapply ParseNullCA.parse_null_ok; d. Qed.
#[local] Hint Resolve parse_null_art : glueA.
Lemma parse_true_art : PMSA.parse_true_specA art_L ar HI IC 794796.
Proof. eapply ParseTrueCA.parse_true_ok; d. Qed.
#[local] Hint Resolve parse_true_art : glueA.
Lemma parse_false_art : PMSA.parse_false_specA art_L ar HI IC 796028.
Proof. eapply ParseFalseCA.parse_false_ok; d. Qed.
#[local] Hint Resolve parse_false_art : glueA.
Lemma begin_object_art : PMSA.begin_object_specA art_L ar HI IC 781384.
Proof. eapply BeginObjectCA.begin_object_ok; d. Qed.
#[local] Hint Resolve begin_object_art : glueA.
Lemma begin_array_art : PMSA.begin_array_specA art_L ar HI IC 782284.
Proof. eapply BeginArrayCA.begin_array_ok; d. Qed.
#[local] Hint Resolve begin_array_art : glueA.
Lemma end_object_art : PMSA.end_object_specA art_L ar HI IC 797332.
Proof. eapply EndObjectCA.end_object_ok; d. Qed.
#[local] Hint Resolve end_object_art : glueA.
Lemma end_array_art : PMSA.end_array_specA art_L ar HI IC 798824.
Proof. eapply EndArrayCA.end_array_ok; d. Qed.
#[local] Hint Resolve end_array_art : glueA.
Lemma skip_space_art : PMSA.skip_space_specA art_L ar HI IC 780684.
Proof. eapply SkipSpaceCA.skip_space_ok; d. Qed.
#[local] Hint Resolve skip_space_art : glueA.
Lemma validate_art : PMSA.validate_specA art_L ar HI IC 812976.
Proof. eapply ValidateCA.validate_ok; d. Qed.
#[local] Hint Resolve validate_art : glueA.
Lemma dec_u64_art : PMSA.dec_u64_specA art_L ar HI IC 806728.
Proof. eapply DecU64CA.dec_u64_ok; d. Qed.
#[local] Hint Resolve dec_u64_art : glueA.
Lemma end_negative_value_art : PMSA.end_number_specA art_L ar HI IC 801960.
Proof. eapply EndNegativeValueCA.end_negative_value_ok; d. Qed.
#[local] Hint Resolve end_negative_value_art : glueA.
Lemma end_positive_value_art : PMSA.end_number_specA art_L ar HI IC 803424.
Proof. eapply EndPositiveValueCA.end_positive_value_ok; d. Qed.
#[local] Hint Resolve end_positive_value_art : glueA.
Lemma end_integer_value_art : PMSA.end_integer_value_specA art_L ar HI IC 778024.
Proof. eapply EndIntegerValueCA.end_integer_value_ok; d. Qed.
#[local] Hint Resolve end_integer_value_art : glueA.
Lemma decstr_art : PMSA.decstr_to_double_specA art_L ar HI IC 805108.
Proof. eapply DecstrCA.decstr_ok; d. Qed.
#[local] Hint Resolve decstr_art : glueA.
Lemma end_fraction_value_art : PMSA.end_fraction_value_specA art_L ar HI IC 778200.
Proof. eapply EndFractionValueCA.end_fraction_value_ok; d. Qed.
#[local] Hint Resolve end_fraction_value_art : glueA.
Lemma tce_art : PMSA.translate_conv_errc_specA art_L ar HI IC 813908.
Proof. eapply TceCA.tce_ok; d. Qed.
#[local] Hint Resolve tce_art : glueA.
Lemma end_string_value_art : PMSA.end_string_value_specA art_L ar HI IC 808628.
Proof. eapply EndStringValueCA.end_string_value_ok; d. Qed.
#[local] Hint Resolve end_string_value_art : glueA.
Lemma atc_art : PMSA.append_to_codepoint_specA art_L ar HI IC 811840.
Proof. eapply AtcCA.atc_ok; d. Qed.
#[local] Hint Resolve atc_art : glueA.
Lemma str_reserve_art : PMSA.str_reserve_specA art_L ar HI 983892.
Proof. eapply StrReserveCA.str_reserve_ok; d. Qed.
#[local] Hint Resolve str_reserve_art : glueA.
Lemma str_push_back_art : PMSA.str_push_back_specA art_L ar HI 985020.
Proof. eapply StrPushBackCA.str_push_back_ok; d. Qed.
#[local] Hint Resolve str_push_back_art : glueA.
Lemma str_append_art : PMSA.str_append_specA art_L ar HI 984436.
Proof. eapply StrAppendCA.str_append_ok; d. Qed.
#[local] Hint Resolve str_append_art : glueA.
Lemma str_append_range_art : PMSA.str_append_range_specA art_L ar HI 815328.
Proof. eapply StrAppendRangeCA.str_append_range_ok; d. Qed.
#[local] Hint Resolve str_append_range_art : glueA.
Lemma convert_art : PMSA.convert_specA art_L ar HI 812508.
Proof. eapply ConvertCA.convert_ok; d. Qed.
#[local] Hint Resolve convert_art : glueA.
Lemma parse_string_art : PMSA.parse_string_specA art_L ar HI IC 783228.
Proof. eapply ParseStringCA.parse_string_ok; d. Qed.
#[local] Hint Resolve parse_string_art : glueA.
Lemma parse_number_art : PMSA.parse_number_specA art_L ar HI IC 789464.
Proof. eapply ParseNumberCA.parse_number_ok; d. Qed.
#[local] Hint Resolve parse_number_art : glueA.
Lemma strinit_art : PMSA.strinit_specA art_L ar HI 719088.
Proof. eapply StrInitCA.strinit_ok; d. Qed.
#[local] Hint Resolve strinit_art : glueA.
Lemma system_category_art : PMSA.system_category_specA art_L ar HI IC 1002208.
Proof. eapply SyscatCA.system_category_ok; d. Qed.
#[local] Hint Resolve system_category_art : glueA.
Lemma locale_ctor_later_art : PMSA.locale_ctor_later_specA art_L ar HI IC 1156200.
Proof. eapply LocaleCA.locale_ctor_later_ok; d. Qed.
#[local] Hint Resolve locale_ctor_later_art : glueA.
Lemma locale_dtor_art : PMSA.locale_dtor_specA art_L ar HI IC 1156416.
Proof. eapply LocaleDtorCA.locale_dtor_ok; d. Qed.
#[local] Hint Resolve locale_dtor_art : glueA.
Lemma atexit_handler_art : forall ILX0 : icpt_layout_x, PMSA.atexit_handler_specA art_L ar HI IC ILX0.
Proof. intros ILX0. eapply (AtexitHandlerCA.atexit_handler_ok _ _ _ _); d. Qed.
#[local] Hint Resolve atexit_handler_art : glueA.
Lemma parser_dtor_art : PMSA.parser_dtor_specA art_L ar HI IC 725196.
Proof. eapply ParserDtorCA.parser_dtor_ok; d. Qed.
#[local] Hint Resolve parser_dtor_art : glueA.
Lemma source_dtor_art : PMSA.source_dtor_specA art_L ar HI IC 726828.
Proof. eapply SourceDtorCA.source_dtor_ok; d. Qed.
#[local] Hint Resolve source_dtor_art : glueA.
Lemma iss_ctor_art : PMSA.iss_ctor_specA art_L ar HI IC 719432.
Proof. eapply IssCtorCA.iss_ctor_ok; d. Qed.
#[local] Hint Resolve iss_ctor_art : glueA.
Lemma detect_json_art : TopSpecsCA.TPSA.detect_json_specA art_L ar HI IC 747556.
Proof. eapply DetectCA.detect_json_ok; d. Qed.
#[local] Hint Resolve detect_json_art : glueA.
Lemma xsgetn_art : TopSpecsCA.TPSA.xsgetn_specA art_L ar HI IC 1007104.
Proof. eapply XsgetnCA.xsgetn_ok; d. Qed.
#[local] Hint Resolve xsgetn_art : glueA.
Lemma iss_ctorX_art : HnKitCA.HNK.iss_ctor_specX art_L ar HI IC 719432.
Proof. eapply IssCtorCA.iss_ctor_okX; d. Qed.
#[local] Hint Resolve iss_ctorX_art : glueA.

Lemma parse_some_art : PMSA.parse_some_specA art_L ar HI IC 748972.
Proof. eapply ParseSomeCA.PSOA_TOP.parse_some_ok; d. Qed.
#[local] Hint Resolve parse_some_art : glueA.

End Inst.
End GLC.
