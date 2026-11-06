(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9IcptLayout Pm9L5DefsA Pm9ArtFsInv Pm9ArtIfaceInst Pm9ArtIfaceInstX PmLibAssemblyCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutRtCpsA.

From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require TopSpecsCB AfterValueCB AnnotateCB AnnotateNullCB AtcCB AtexitHandlerCB BeginArrayCB BeginMemberCB BeginObjectCB ConvertCB DecU64CB DecstrCB DetectCB EndArrayCB EndFractionValueCB EndIntegerValueCB EndNegativeValueCB EndObjectCB EndPositiveValueCB EndStringValueCB ErrHandlerCB GuardCB IssCtorCB LocaleCB LocaleDtorCB OpDelCB OpDelNullCB OpNewCB ParentCB ParseFalseCB ParseNullCB ParseNumberCB ParseStringCB ParseTrueCB ParserDtorCB PopStateCB SetEcCB SkipSpaceCB SourceDtorCB StrAppendCB StrAppendRangeCB StrInitCB StrPushBackCB StrReserveCB SyscatCB TceCB ValidateCB VecDtorCB VecPushCB VecPushSlowCB VecReserveCB XsgetnCB VisitNullCB VisitBoolCB VisitU64CB VisitI64CB VisitDoubleCB VisitKeyCB VisitStringCB VisitBeginObjCB VisitBeginArrCB VisitEndObjCB VisitEndArrCB ParseSomeCB IslCgCB HnKitCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PmLibSpecsBLocal.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmIslandInstCB Pm9StrtodOk Pm9FloatLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GLCB.
Abbreviation IC := PMLA.C_cboth.
Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

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
Let LAY := ASMCB.art_lay.
Let FPM := ASMCB.art_fpm.
Let FOOTC := ASMCB.art_footc.
Lemma FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.
Proof.
  intros a (iv & Hin & Hr). cbn [art_L hl_rt_static hl_rt_ro]. unfold art_static, art_ro.
  cbn [PMLA.FOOT PMLA.C_cboth In] in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
Let ISH : rt_img_shadow art_L IL HI := pic_img_shadow _ _ _ _ _ _ _ ICok.
Lemma ANN : aannotate_spec art_L ar scfg HI 0x8301c 4096.
Proof. rewrite <- (aiclx_annotate ILX ILXok). exact (pic_annotate _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMSET_LIBC : CRC.amemset_spec_at art_L ar HI 0x7f228.
Proof.
  rewrite <- (aiclx_memset ILX ILXok).
  intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt).
Qed.
Lemma MEMCPY_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7f230 false.
Proof. rewrite <- (aicl_memcpy IL ILok). exact (pic_memcpy_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMMOVE_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7f22c false.
Proof. rewrite <- (aicl_memmove IL ILok). exact (pic_memmove_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMCMP_TU : amemcmp_spec_at art_L ar scfg HI 0x6a924 8192.
Proof. rewrite <- (aiclx_memcmp ILX ILXok), <- (aiclx_scr_memcmp ILX ILXok). exact (pic_memcmp _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF5 : aset_shadow_spec art_L ar scfg HI 0x82eac 245 256.
Proof. rewrite <- (aiclx_setshf5 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf5 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSH00 : aset_shadow_spec art_L ar scfg HI 0x82da4 0 256.
Proof. rewrite <- (aiclx_setsh00 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setsh00 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF8 : aset_shadow_spec art_L ar scfg HI 0x82ec4 248 256.
Proof. rewrite <- (aiclx_setshf8 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf8 _ _ _ _ _ _ _ ICok). Qed.

Lemma SF5 : PmHeapIfaceA.astack_free_spec art_L ar scfg HI 0x65888 0x103a8 5.
Proof. rewrite <- ASMCB.art_sfree5, <- ASMCB.art_sfree_pat. exact (pio_stack_free5 _ _ _ _ _ _ HIok). Qed.
Lemma PATR : 0x10000 <= 0x103a8 /\ 0x103a8 + 8 <= 0x156000.
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

Lemma strtod_art : PMSA.strtod_specA art_L ar HI IC 0x145768.
Proof. exact (Pm9StrtodOk.STOA.strtod_okA art_L ar art_C HI HIok0 LAY Pm9FloatLayout.art_float). Qed.
#[local] Hint Resolve strtod_art : glueA.

Lemma locale_ctor_first_art : PMSA.locale_ctor_first_specA art_L ar HI IC 0x11b984.
Proof. exact (PmIslandInstCB.ISAI9.locale_ctor_first_art scfg ar HI IL ILX _ ILok ILXok HIok ICok). Qed.
#[local] Hint Resolve locale_ctor_first_art : glueA.
Lemma locale_ctor_first_cg_art : IslCgCB.ICG.locale_ctor_first_specA_cg art_L ar HI IC 0x11b984.
Proof. exact (PmIslandInstCB.ISAI9.locale_ctor_first_art_cg scfg ar HI IL ILX _ ILok ILXok HIok ICok). Qed.
#[local] Hint Resolve locale_ctor_first_cg_art : glueA.

Lemma visit_null_art : PMSA.visit_null_specA art_L ar HI IC 0xcb418.
Proof. eapply VisitNullCB.visit_null_ok; d. Qed.
#[local] Hint Resolve visit_null_art : glueA.
Lemma visit_bool_art : PMSA.visit_bool_specA art_L ar HI IC 0xcb4c0.
Proof. eapply VisitBoolCB.visit_bool_ok; d. Qed.
#[local] Hint Resolve visit_bool_art : glueA.
Lemma visit_u64_art : PMSA.visit_u64_specA art_L ar HI IC 0xcadd4.
Proof. eapply VisitU64CB.visit_u64_ok; d. Qed.
#[local] Hint Resolve visit_u64_art : glueA.
Lemma visit_i64_art : PMSA.visit_i64_specA art_L ar HI IC 0xcaea4.
Proof. eapply VisitI64CB.visit_i64_ok; d. Qed.
#[local] Hint Resolve visit_i64_art : glueA.
Lemma visit_double_art : PMSA.visit_double_specA art_L ar HI IC 0xcaf74.
Proof. eapply VisitDoubleCB.visit_double_ok; d. Qed.
#[local] Hint Resolve visit_double_art : glueA.
Lemma visit_key_art : PMSA.visit_key_specA art_L ar HI IC 0xcb308.
Proof. eapply VisitKeyCB.visit_key_ok; d. Qed.
#[local] Hint Resolve visit_key_art : glueA.
Lemma visit_string_art : PMSA.visit_string_specA art_L ar HI IC 0xcb598.
Proof. eapply VisitStringCB.visit_string_ok; d. Qed.
#[local] Hint Resolve visit_string_art : glueA.
Lemma visit_begin_object_art : PMSA.visit_begin_object_specA art_L ar HI IC 0xcb048.
Proof. eapply VisitBeginObjCB.visit_begin_object_ok; d. Qed.
#[local] Hint Resolve visit_begin_object_art : glueA.
Lemma visit_begin_array_art : PMSA.visit_begin_array_specA art_L ar HI IC 0xcb260.
Proof. eapply VisitBeginArrCB.visit_begin_array_ok; d. Qed.
#[local] Hint Resolve visit_begin_array_art : glueA.
Lemma visit_end_object_art : PMSA.visit_end_object_specA art_L ar HI IC 0xcb1c4.
Proof. eapply VisitEndObjCB.visit_end_object_ok; d. Qed.
#[local] Hint Resolve visit_end_object_art : glueA.
Lemma visit_end_array_art : PMSA.visit_end_array_specA art_L ar HI IC 0xcad34.
Proof. eapply VisitEndArrCB.visit_end_array_ok; d. Qed.
#[local] Hint Resolve visit_end_array_art : glueA.

Lemma opnew_art : PMSA.opnew_specA art_L ar HI 1363704.
Proof. eapply OpNewCB.opnew_ok; d. Qed.
#[local] Hint Resolve opnew_art : glueA.
Lemma opdel_art : PMSA.opdel_specA art_L ar HI 980676.
Proof. eapply OpDelCB.opdel_ok; d. Qed.
#[local] Hint Resolve opdel_art : glueA.
Lemma opdel_sized_art : PMSA.opdel_specA art_L ar HI 980680.
Proof. eapply OpDelCB.opdel_sized_ok; d. Qed.
#[local] Hint Resolve opdel_sized_art : glueA.
Lemma opdel_null_art : PMSA.opdel_null_specA art_L ar HI 980676.
Proof. eapply OpDelNullCB.opdel_null_ok; d. Qed.
#[local] Hint Resolve opdel_null_art : glueA.
Lemma guard_acquire_art : PMSA.guard_acquire_specA art_L ar HI 863640.
Proof. eapply GuardCB.guard_acquire_ok; d. Qed.
#[local] Hint Resolve guard_acquire_art : glueA.
Lemma guard_release_art : PMSA.guard_release_specA art_L ar HI 863720.
Proof. eapply GuardCB.guard_release_ok; d. Qed.
#[local] Hint Resolve guard_release_art : glueA.
Lemma annotate_increase_art : PMSB.annotate_increase_spec art_L ar HI 808928.
Proof. eapply AnnotateCB.annotate_increase_ok; d. Qed.
#[local] Hint Resolve annotate_increase_art : glueA.
Lemma annotate_shrink_art : PMSB.annotate_shrink_spec art_L ar HI 727976.
Proof. eapply AnnotateCB.annotate_shrink_ok; d. Qed.
#[local] Hint Resolve annotate_shrink_art : glueA.
Lemma annotate_new_art : PMSA.annotate_new_spec art_L ar HI 810224.
Proof. eapply AnnotateCB.annotate_new_ok; d. Qed.
#[local] Hint Resolve annotate_new_art : glueA.
Lemma annotate_delete_art : PMSA.annotate_delete_spec art_L ar HI 727788.
Proof. eapply AnnotateCB.annotate_delete_ok; d. Qed.
#[local] Hint Resolve annotate_delete_art : glueA.
Lemma annotate_delete_null_art : PMSA.annotate_delete_null_spec art_L ar HI 727788.
Proof. eapply AnnotateNullCB.annotate_delete_null_ok; d. Qed.
#[local] Hint Resolve annotate_delete_null_art : glueA.
Lemma vec_push_slow_art : PMSA.vec_push_slow_spec art_L ar HI 808308.
Proof. eapply VecPushSlowCB.vec_push_slow_ok; d. Qed.
#[local] Hint Resolve vec_push_slow_art : glueA.
Lemma vec_push_art : PMSA.vec_push_specA art_L ar HI 807908.
Proof. eapply VecPushCB.vec_push_ok; d. Qed.
#[local] Hint Resolve vec_push_art : glueA.
Lemma pop_state_art : PMSB.pop_state_specA art_L ar HI 780820.
Proof. eapply PopStateCB.pop_state_ok; d. Qed.
#[local] Hint Resolve pop_state_art : glueA.
Lemma parent_art : PMSA.parent_specA art_L ar HI 801208.
Proof. eapply ParentCB.parent_ok; d. Qed.
#[local] Hint Resolve parent_art : glueA.
Lemma vec_dtor_art : PMSA.vec_dtor_specA art_L ar HI 727360.
Proof. eapply VecDtorCB.vec_dtor_ok; d. Qed.
#[local] Hint Resolve vec_dtor_art : glueA.
Lemma vec_reserve_art : PMSA.vec_reserve_specA art_L ar HI 829676.
Proof. eapply VecReserveCB.vec_reserve_ok; d. Qed.
#[local] Hint Resolve vec_reserve_art : glueA.
Lemma after_value_art : PMSA.after_value_specA art_L ar HI IC 806480.
Proof. eapply AfterValueCB.after_value_ok; d. Qed.
#[local] Hint Resolve after_value_art : glueA.
Lemma begin_member_art : PMSA.begin_member_specA art_L ar HI IC 800616.
Proof. eapply BeginMemberCB.begin_member_ok; d. Qed.
#[local] Hint Resolve begin_member_art : glueA.
Lemma errh_art : PMSA.errh_specA art_L ar HI 824952.
Proof. eapply ErrHandlerCB.errh_ok; d. Qed.
#[local] Hint Resolve errh_art : glueA.
Lemma set_ec_art : PMSA.set_ec_specA art_L ar HI IC 749196.
Proof. eapply SetEcCB.set_ec_ok; d. Qed.
#[local] Hint Resolve set_ec_art : glueA.
Lemma parse_null_art : PMSA.parse_null_specA art_L ar HI IC 794316.
Proof. eapply ParseNullCB.parse_null_ok; d. Qed.
#[local] Hint Resolve parse_null_art : glueA.
Lemma parse_true_art : PMSA.parse_true_specA art_L ar HI IC 795580.
Proof. eapply ParseTrueCB.parse_true_ok; d. Qed.
#[local] Hint Resolve parse_true_art : glueA.
Lemma parse_false_art : PMSA.parse_false_specA art_L ar HI IC 796780.
Proof. eapply ParseFalseCB.parse_false_ok; d. Qed.
#[local] Hint Resolve parse_false_art : glueA.
Lemma begin_object_art : PMSA.begin_object_specA art_L ar HI IC 782464.
Proof. eapply BeginObjectCB.begin_object_ok; d. Qed.
#[local] Hint Resolve begin_object_art : glueA.
Lemma begin_array_art : PMSA.begin_array_specA art_L ar HI IC 783312.
Proof. eapply BeginArrayCB.begin_array_ok; d. Qed.
#[local] Hint Resolve begin_array_art : glueA.
Lemma end_object_art : PMSA.end_object_specA art_L ar HI IC 798060.
Proof. eapply EndObjectCB.end_object_ok; d. Qed.
#[local] Hint Resolve end_object_art : glueA.
Lemma end_array_art : PMSA.end_array_specA art_L ar HI IC 799336.
Proof. eapply EndArrayCB.end_array_ok; d. Qed.
#[local] Hint Resolve end_array_art : glueA.
Lemma skip_space_art : PMSA.skip_space_specA art_L ar HI IC 781716.
Proof. eapply SkipSpaceCB.skip_space_ok; d. Qed.
#[local] Hint Resolve skip_space_art : glueA.
Lemma validate_art : PMSA.validate_specA art_L ar HI IC 814840.
Proof. eapply ValidateCB.validate_ok; d. Qed.
#[local] Hint Resolve validate_art : glueA.
Lemma dec_u64_art : PMSA.dec_u64_specA art_L ar HI IC 807072.
Proof. eapply DecU64CB.dec_u64_ok; d. Qed.
#[local] Hint Resolve dec_u64_art : glueA.
Lemma end_negative_value_art : PMSA.end_number_specA art_L ar HI IC 802200.
Proof. eapply EndNegativeValueCB.end_negative_value_ok; d. Qed.
#[local] Hint Resolve end_negative_value_art : glueA.
Lemma end_positive_value_art : PMSA.end_number_specA art_L ar HI IC 803696.
Proof. eapply EndPositiveValueCB.end_positive_value_ok; d. Qed.
#[local] Hint Resolve end_positive_value_art : glueA.
Lemma end_integer_value_art : PMSA.end_integer_value_specA art_L ar HI IC 779000.
Proof. eapply EndIntegerValueCB.end_integer_value_ok; d. Qed.
#[local] Hint Resolve end_integer_value_art : glueA.
Lemma decstr_art : PMSA.decstr_to_double_specA art_L ar HI IC 805428.
Proof. eapply DecstrCB.decstr_ok; d. Qed.
#[local] Hint Resolve decstr_art : glueA.
Lemma end_fraction_value_art : PMSA.end_fraction_value_specA art_L ar HI IC 779184.
Proof. eapply EndFractionValueCB.end_fraction_value_ok; d. Qed.
#[local] Hint Resolve end_fraction_value_art : glueA.
Lemma tce_art : PMSA.translate_conv_errc_specA art_L ar HI IC 815932.
Proof. eapply TceCB.tce_ok; d. Qed.
#[local] Hint Resolve tce_art : glueA.
Lemma end_string_value_art : PMSB.end_string_value_specA art_L ar HI IC 810388.
Proof. eapply EndStringValueCB.end_string_value_ok; d. Qed.
#[local] Hint Resolve end_string_value_art : glueA.
Lemma atc_art : PMSA.append_to_codepoint_specA art_L ar HI IC 813608.
Proof. eapply AtcCB.atc_ok; d. Qed.
#[local] Hint Resolve atc_art : glueA.
Lemma str_reserve_art : PMSA.str_reserve_specA art_L ar HI 989296.
Proof. eapply StrReserveCB.str_reserve_ok; d. Qed.
#[local] Hint Resolve str_reserve_art : glueA.
Lemma str_push_back_art : PMSA.str_push_back_specA art_L ar HI 990424.
Proof. eapply StrPushBackCB.str_push_back_ok; d. Qed.
#[local] Hint Resolve str_push_back_art : glueA.
Lemma str_append_art : PMSA.str_append_specA art_L ar HI 989840.
Proof. eapply StrAppendCB.str_append_ok; d. Qed.
#[local] Hint Resolve str_append_art : glueA.
Lemma str_append_range_art : PMSA.str_append_range_specA art_L ar HI 816864.
Proof. eapply StrAppendRangeCB.str_append_range_ok; d. Qed.
#[local] Hint Resolve str_append_range_art : glueA.
Lemma convert_art : PMSB.convert_specA art_L ar HI IC 814184.
Proof. eapply ConvertCB.convert_ok; d. Qed.
#[local] Hint Resolve convert_art : glueA.
Lemma parse_string_art : PMSA.parse_string_specA art_L ar HI IC 784204.
Proof. eapply ParseStringCB.parse_string_ok; d. Qed.
#[local] Hint Resolve parse_string_art : glueA.
Lemma parse_number_art : PMSA.parse_number_specA art_L ar HI IC 790556.
Proof. eapply ParseNumberCB.parse_number_ok; d. Qed.
#[local] Hint Resolve parse_number_art : glueA.
Lemma strinit_art : PMSA.strinit_specA art_L ar HI 720088.
Proof. eapply StrInitCB.strinit_ok; d. Qed.
#[local] Hint Resolve strinit_art : glueA.
Lemma system_category_art : PMSA.system_category_specA art_L ar HI IC 1007612.
Proof. eapply SyscatCB.system_category_ok; d. Qed.
#[local] Hint Resolve system_category_art : glueA.
Lemma locale_ctor_later_art : PMSA.locale_ctor_later_specA art_L ar HI IC 1161604.
Proof. eapply LocaleCB.locale_ctor_later_ok; d. Qed.
#[local] Hint Resolve locale_ctor_later_art : glueA.
Lemma locale_dtor_art : PMSA.locale_dtor_specA art_L ar HI IC 1161820.
Proof. eapply LocaleDtorCB.locale_dtor_ok; d. Qed.
#[local] Hint Resolve locale_dtor_art : glueA.
Lemma atexit_handler_art : forall ILX0 : icpt_layout_x, PMSA.atexit_handler_specA art_L ar HI IC ILX0.
Proof. intros ILX0. eapply (AtexitHandlerCB.atexit_handler_ok _ _ _ _); d. Qed.
#[local] Hint Resolve atexit_handler_art : glueA.
Lemma parser_dtor_art : PMSA.parser_dtor_specA art_L ar HI IC 726328.
Proof. eapply ParserDtorCB.parser_dtor_ok; d. Qed.
#[local] Hint Resolve parser_dtor_art : glueA.
Lemma source_dtor_art : PMSA.source_dtor_specA art_L ar HI IC 728272.
Proof. eapply SourceDtorCB.source_dtor_ok; d. Qed.
#[local] Hint Resolve source_dtor_art : glueA.
Lemma iss_ctor_art : PMSA.iss_ctor_specA art_L ar HI IC 720448.
Proof. eapply IssCtorCB.iss_ctor_ok; d. Qed.
#[local] Hint Resolve iss_ctor_art : glueA.
Lemma detect_json_art : TopSpecsCB.TPSA.detect_json_specA art_L ar HI IC 750032.
Proof. eapply DetectCB.detect_json_ok; d. Qed.
#[local] Hint Resolve detect_json_art : glueA.
Lemma xsgetn_art : TopSpecsCB.TPSA.xsgetn_specA art_L ar HI IC 1012508.
Proof. eapply XsgetnCB.xsgetn_ok; d. Qed.
#[local] Hint Resolve xsgetn_art : glueA.
Lemma iss_ctorX_art : HnKitCB.HNK.iss_ctor_specX art_L ar HI IC 720448.
Proof. eapply IssCtorCB.iss_ctor_okX; d. Qed.
#[local] Hint Resolve iss_ctorX_art : glueA.

Lemma parse_some_art : PMSA.parse_some_specA art_L ar HI IC 751580.
Proof. eapply ParseSomeCB.PSOA_TOP.parse_some_ok; d. Qed.
#[local] Hint Resolve parse_some_art : glueA.

End Inst.
End GLCB.
