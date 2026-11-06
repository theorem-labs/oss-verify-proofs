(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs PmCurSpecsA PmFloatCSpecsA PmFloatCWD HnSpecCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8IcptLayout Pm8L5DefsA Pm8ArtFsInv Pm8ArtIfaceInst Pm8ArtIfaceInstX PmLibAssemblyCA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmCasanFinal PmLibGlueCA Pm8StrtodG DecstrGCA Pm8FloatLayout.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FloatCA Require SnprintfCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutRtCpsA.

From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require TopSpecsCA HnKitCA SetEc2CA ConvEcCA StrInit2CA RChunkCurCA ReadNextCA CursorMainCA CursorCtorCA CStrCA GetLitCA GetStrCA FromIntCA FromInt64CA
  HarnessAsCA HarnessAlCA HarnessBsCA HarnessBlCA LibTopCA StrPushShortCA DumpBufCA PrettifyCA DtoaFalseCA DtoaTrueCA WriteDoubleCA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmCasanLibTop.
Abbreviation IC := PMLA.C_casan.
Module G := PmLibGlueCA.GLC.

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
Let ISH : rt_img_shadow art_L IL HI := pic_img_shadow _ _ _ _ _ _ _ ICok.
Let RTG : rt_globals IL HI := pic_globals _ _ _ _ _ _ _ ICok.
Let STRLEN : astrlen_spec art_L ar IL scfg HI := pic_strlen _ _ _ _ _ _ _ ICok.
Lemma FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.  Proof. exact G.FOOTC2. Qed.
Lemma MEMSET_LIBC : CRC.amemset_spec_at art_L ar HI 0x7ee68.  Proof. eapply G.MEMSET_LIBC; eassumption. Qed.
Lemma SETSHF5 : aset_shadow_spec art_L ar scfg HI 0x82aec 245 256.  Proof. eapply G.SETSHF5; eassumption. Qed.
Lemma SETSH00 : aset_shadow_spec art_L ar scfg HI 0x829e4 0 256.  Proof. eapply G.SETSH00; eassumption. Qed.
Lemma SETSHF8 : aset_shadow_spec art_L ar scfg HI 0x82b04 248 256.  Proof. eapply G.SETSHF8; eassumption. Qed.
Lemma SF5 : PmHeapIfaceA.astack_free_spec art_L ar scfg HI 0x654c8 0x10398 5.  Proof. eapply G.SF5; eassumption. Qed.
Lemma PATR : 0x10000 <= 0x10398 /\ 0x10398 + 8 <= 0x154000.  Proof. lia. Qed.
Lemma TPV0 : hl_tp art_L = 6883920.  Proof. exact ASMC.art_tp. Qed.
Lemma TPV : hl_tp art_L - 164 = 6883756.  Proof. rewrite TPV0. reflexivity. Qed.
Lemma MEMMOVE_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7ee6c false.  Proof. eapply G.MEMMOVE_LIBC; eassumption. Qed.
Lemma MEMCPY_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7ee70 false.  Proof. eapply G.MEMCPY_LIBC; eassumption. Qed.
Let RSD : rt_shadow_defined HI := pic_shadow_defined _ _ _ _ _ _ _ ICok.
Lemma incl_of_b : forall (l1 l2 : list (Z * Z * Z)),
  forallb (fun x => existsb (fun y => (fst (fst x) =? fst (fst y)) && (snd (fst x) =? snd (fst y)) && (snd x =? snd y)) l2) l1 = true -> incl l1 l2.
Proof.
  intros l1 l2 H x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply existsb_exists in H as (y & Hy & E).
  apply andb_prop in E as (E & E3). apply andb_prop in E as (E1 & E2). apply Z.eqb_eq in E1, E2, E3.
  destruct x as [[a b] c], y as [[a' b'] c']. cbn in *. subst. exact Hy.
Qed.

Lemma strinit_art : PMSA.strinit_specA art_L ar HI 719088.                          Proof. eapply G.strinit_art; eassumption. Qed.
Lemma iss_ctorX_art : HnKitCA.HNK.iss_ctor_specX art_L ar HI IC 719432.             Proof. eapply G.iss_ctorX_art; eassumption. Qed.
Lemma system_category_art : PMSA.system_category_specA art_L ar HI IC 1002208.      Proof. eapply G.system_category_art; eassumption. Qed.
Lemma parser_dtor_art : PMSA.parser_dtor_specA art_L ar HI IC 725196.                Proof. eapply G.parser_dtor_art; eassumption. Qed.
Lemma source_dtor_art : PMSA.source_dtor_specA art_L ar HI IC 726828.                Proof. eapply G.source_dtor_art; eassumption. Qed.
Lemma locale_dtor_art : PMSA.locale_dtor_specA art_L ar HI IC 1156416.              Proof. eapply G.locale_dtor_art; eassumption. Qed.
Lemma locale_ctor_later_art : PMSA.locale_ctor_later_specA art_L ar HI IC 1156200.  Proof. eapply G.locale_ctor_later_art; eassumption. Qed.
Lemma opdel_art : PMSA.opdel_specA art_L ar HI 975272.                               Proof. eapply G.opdel_art; eassumption. Qed.
Lemma opnew_art : PMSA.opnew_specA art_L ar HI 1358140.                              Proof. eapply G.opnew_art; eassumption. Qed.
Lemma str_reserve_art : PMSA.str_reserve_specA art_L ar HI 983892.                   Proof. eapply G.str_reserve_art; eassumption. Qed.
Lemma vec_reserve_art : PMSA.vec_reserve_specA art_L ar HI 827068.                   Proof. eapply G.vec_reserve_art; eassumption. Qed.
Lemma vec_push_art : PMSA.vec_push_specA art_L ar HI 807200.                         Proof. eapply G.vec_push_art; eassumption. Qed.
Lemma guard_acquire_art : PMSA.guard_acquire_specA art_L ar HI 858236.               Proof. eapply G.guard_acquire_art; eassumption. Qed.
Lemma guard_release_art : PMSA.guard_release_specA art_L ar HI 858316.               Proof. eapply G.guard_release_art; eassumption. Qed.
Lemma set_ec_art : PMSA.set_ec_specA art_L ar HI IC 747008.                          Proof. eapply G.set_ec_art; eassumption. Qed.
Lemma parse_some_art : PMSA.parse_some_specA art_L ar HI IC 748972.                  Proof. eapply G.parse_some_art; eassumption. Qed.
Lemma detect_json_art : TopSpecsCA.TPSA.detect_json_specA art_L ar HI IC 747556.     Proof. eapply G.detect_json_art; eassumption. Qed.
Lemma xsgetn_art : TopSpecsCA.TPSA.xsgetn_specA art_L ar HI IC 1007104.              Proof. eapply G.xsgetn_art; eassumption. Qed.

Ltac poi := rewrite (aicl_poison IL ILok); unfold ART_POISON; cbv -[Z.le Z.lt Z.add fst snd];
            repeat first [ apply Forall_nil | apply Forall_cons | (cbn [fst snd]; lia) ].
Ltac ilxeq := first [ rewrite (aiclx_cxa_atexit ILX ILXok) | rewrite (aiclx_scr_cxa ILX ILXok) | rewrite (aiclx_atexit_tab ILX ILXok)
                     | rewrite (aiclx_atcxa ILX ILXok) | rewrite (aiclx_need_locks ILX ILXok) ]; first [ reflexivity | lia ].
Ltac icleq := first [ rewrite (aicl_strlen IL ILok) | rewrite (aicl_scr_strlen IL ILok) | rewrite (aicl_ro_lo IL ILok) | rewrite (aicl_ro_hi IL ILok) ];
              first [ reflexivity | lia | (split; cbv; lia) ].
Ltac inlist := repeat (first [ left; reflexivity | right ]).
Ltac ilg := intros ?ch ?Hch; rewrite (aicl_globals IL ILok); unfold ART_GLOBALS;
            destruct ch as [|[|[|?ch]]]; [ cbv; inlist | cbv; inlist | cbv; inlist | exfalso; clear - Hch; lia ].
Ltac client_rng := intros ?a0 ?Ha0; cbn [art_L hl_rt_static hl_rt_ro]; unfold art_static, art_ro;
                   cbv -[Z.le Z.lt Z.ge Z.gt Z.add Z.sub not] in Ha0; lia.
Ltac rows := lazymatch goal with
  | |- PMSA.strinit_specA _ _ _ ?pc => first [ exact strinit_art | exact (StrInit2CA.strinit2_ok _ _ _ _ HIok0 LAY FPM opnew_art) ]
  | |- HnKitCA.HNK.iss_ctor_specX _ _ _ _ _ => exact iss_ctorX_art
  | |- PMSA.system_category_specA _ _ _ _ _ => exact system_category_art
  | |- PMSA.parser_dtor_specA _ _ _ _ _ => exact parser_dtor_art
  | |- PMSA.source_dtor_specA _ _ _ _ _ => exact source_dtor_art
  | |- PMSA.locale_dtor_specA _ _ _ _ _ => exact locale_dtor_art
  | |- PMSA.locale_ctor_later_specA _ _ _ _ _ => exact locale_ctor_later_art
  | |- PMSA.opdel_specA _ _ _ _ => exact opdel_art
  | |- PMSA.opnew_specA _ _ _ _ => exact opnew_art
  | |- PMSA.str_reserve_specA _ _ _ _ => exact str_reserve_art
  | |- PMSA.vec_reserve_specA _ _ _ _ => exact vec_reserve_art
  | |- PMSA.vec_push_specA _ _ _ _ => exact vec_push_art
  | |- PMSA.guard_acquire_specA _ _ _ _ => exact guard_acquire_art
  | |- PMSA.guard_release_specA _ _ _ _ => exact guard_release_art
  | |- PMSA.set_ec_specA _ _ _ _ _ => exact set_ec_art
  | |- PMSA.parse_some_specA _ _ _ _ _ => exact parse_some_art
  | |- TopSpecsCA.TPSA.detect_json_specA _ _ _ _ _ => exact detect_json_art
  | |- TopSpecsCA.TPSA.xsgetn_specA _ _ _ _ _ => exact xsgetn_art
  | |- CRC.amemset_spec_at _ _ _ _ => exact MEMSET_LIBC
  | |- aset_shadow_spec _ _ _ _ _ 245 256 => exact SETSHF5
  | |- aset_shadow_spec _ _ _ _ _ 0 256 => exact SETSH00
  | |- aset_shadow_spec _ _ _ _ _ 248 256 => exact SETSHF8
  | |- PmHeapIfaceA.astack_free_spec _ _ _ _ _ _ _ => exact SF5
  | |- amemcpy_spec_at _ _ _ _ _ _ => first [ exact MEMMOVE_LIBC | exact MEMCPY_LIBC ]
  end.

Ltac facts := lazymatch goal with
  | |- wx_segs_nowrap _ => apply wx_segs_nowrap_of_b; vm_compute; reflexivity
  | |- incl _ _ => apply incl_of_b; vm_compute; reflexivity
  | |- segs_below_b _ _ = true => vm_compute; reflexivity
  | |- hl_stack_malloc _ _ = _ => first [ exact ASMC.art_sm0 | exact ASMC.art_sm1 | exact ASMC.art_sm2 | exact ASMC.art_sm3 | exact ASMC.art_sm4 | exact ASMC.art_sm5 ]
  | |- hl_tp _ = _ => exact TPV0
  | |- hl_tp _ - 164 = _ => exact TPV
  | |- hl_segs _ = _ => reflexivity
  | |- hl_img_lo _ = _ => reflexivity
  | |- hl_img_hi _ = _ => reflexivity
  | |- PMLA.IMG_RO_LO _ = _ /\ PMLA.IMG_RO_HI _ = _ => split; reflexivity
  | |- PMLA.IMG_RO_LO _ <= icl_ro_lo _ /\ icl_ro_hi _ <= PMLA.IMG_RO_HI _ => rewrite (aicl_ro_lo IL ILok), (aicl_ro_hi IL ILok); vm_compute; split; discriminate
  | |- 0 <= hl_img_lo _ /\ hl_img_hi _ <= _ => split; vm_compute; discriminate
  | |- Forall _ (icl_poison _) => poi
  | |- Forall _ (icl_poison _) /\ Forall _ (icl_poison _) => split; poi
  | |- forall _, (_ <= 2)%nat -> In _ (icl_globals _) => ilg
  | |- In _ (icl_globals _) => rewrite (aicl_globals IL ILok); unfold ART_GLOBALS; cbv; inlist
  | |- forall _, hl_rt_ro _ _ -> _ => intros ?a1 ?Ha1; pose proof (art_L_ro_img0 _ Ha1); cbn [art_L hl_img_lo hl_img_hi]; lia
  | |- forall _, _ -> ~ hl_rt_static _ _ /\ ~ hl_rt_ro _ _ => client_rng
  | |- forall _, _ -> ~ hl_rt_static _ _ => client_rng
  | |- iclx_cxa_atexit _ = _ => ilxeq
  | |- 0 <= iclx_scr_cxa _ <= _ => ilxeq
  | |- iclx_atexit_tab _ = _ => ilxeq
  | |- iclx_atcxa _ = _ => ilxeq
  | |- iclx_need_locks _ = _ => ilxeq
  | |- icl_strlen _ = _ => icleq
  | |- 0 <= icl_scr_strlen _ <= _ => icleq
  | |- _ <= _ /\ _ <= _ => exact PATR
  end.
Ltac d := first
  [ exact HIok0 | exact LAY | exact FPM | exact FOOTC | exact FOOTC2 | exact ISH | exact RTG | exact STRLEN | exact ICok | exact FN | exact RSD
  | exact Pm8FloatLayout.art_float
  | rows
  | facts
  | assumption
  | reflexivity ].

Lemma set_ec2_art : PMCSA.set_ec2_specA art_L ar HI IC 825268.            Proof. eapply SetEc2CA.set_ec2_ok; d. Qed.
Lemma conv_ec_art : PMCSA.conv_ec_specA art_L ar HI IC 728032.            Proof. eapply ConvEcCA.conv_ec_ok; d. Qed.
Lemma strinit2_art : PMSA.strinit_specA art_L ar HI 845488.                Proof. eapply StrInit2CA.strinit2_ok; d. Qed.
Lemma read_chunk_c_art : PMCSA.read_chunk_c_specA art_L ar HI IC 746600.  Proof. eapply RChunkCurCA.read_chunk_c_ok; d. Qed.
Lemma read_next_art : PMCSA.read_next_specA art_L ar HI IC 735060.
Proof. eapply ReadNextCA.read_next_ok; first [ exact read_chunk_c_art | d ]. Qed.
Lemma cursor_main_art : PMCSA.cursor_main_specA art_L ar HI IC 819492 1364760 1364800 1364920.
Proof. eapply CursorMainCA.cursor_main_ok; first [ exact read_next_art | exact set_ec2_art | d ]. Qed.
Lemma cursor_ctor_art : PMCSA.cursor_ctor_specA art_L ar HI IC 720100.
Proof. eapply CursorCtorCA.cursor_ctor_ok; first [ exact cursor_main_art | d ]. Qed.

Lemma cstr_art : PMCSA.cstr_ctor_specA art_L ar HI IC 857780.             Proof. eapply CStrCA.cstr_ok; d. Qed.
Lemma from_integer_u64_art : PMFCA.from_integer_u64_specA art_L ar HI IC 839488.  Proof. eapply FromIntCA.from_integer_u64_ok; d. Qed.
Lemma from_integer_i64_art : PMFCA.from_integer_i64_specA art_L ar HI IC 841088.  Proof. eapply FromInt64CA.from_integer_i64_ok; d. Qed.

Lemma push_short_art : PMFCA.str_push_back_short_specA art_L ar HI 985020.   Proof. eapply StrPushShortCA.str_push_back_short_ok; d. Qed.
Lemma push_l48_art : PMFCA.str_push_back_l48_specA art_L ar HI 985020.       Proof. eapply StrPushShortCA.str_push_back_l48_ok; d. Qed.
Ltac dw := first [ exact push_short_art | exact push_l48_art | d ].
Lemma dump_buffer_art : PMFCA.dump_buffer_specA art_L ar HI 847400.          Proof. eapply DumpBufCA.dump_buffer_ok; dw. Qed.
Lemma prettify_art : PMFCA.prettify_specA art_L ar HI 850864.                Proof. eapply PrettifyCA.prettify_ok; dw. Qed.
Lemma strtod_g_art : PMFCA.strtod_g_specA art_L ar HI IC 1327532.            Proof. eapply Pm8StrtodG.STGA.strtod_g_okA; d. Qed.
Lemma decstr_g_art : PMFCA.decstr_to_double_g_specA art_L ar HI IC 805108.   Proof. eapply DecstrGCA.decstr_g_ok; first [ exact strtod_g_art | d ]. Qed.
Lemma snprintf_art : PMFCA.snprintf_g_specA art_L ar HI IC PMFCA.PC_SNPRINTF_casan SnprintfCpsA.FMT_ADDR.  Proof. eapply SnprintfCpsA.snprintf_g_okA; d. Qed.
Lemma dtoa_false_art : PMFCA.dtoa_false_specA art_L ar HI IC 856820.
Proof. eapply DtoaFalseCA.dtoa_false_ok; first [ exact snprintf_art | exact decstr_g_art | exact dump_buffer_art | d ]. Qed.
Lemma dtoa_true_art : PMFCA.dtoa_true_specA art_L ar HI IC 855924.
Proof. eapply DtoaTrueCA.dtoa_true_ok; first [ exact dtoa_false_art | exact prettify_art | d ]. Qed.
Lemma write_double_art : PMFCW.write_double_specW art_L ar HI IC 842800.
Proof. eapply WriteDoubleCA.write_double_ok; first [ exact dtoa_true_art | d ]. Qed.
Lemma get_string_art : PMCSA.get_string_specA art_L ar HI IC 837940.
Proof.
  eapply GetStrCA.get_string_ok;
    first [ exact conv_ec_art | exact cstr_art | exact strinit2_art | exact from_integer_i64_art | exact from_integer_u64_art | exact write_double_art | d ].
Qed.

Ltac hd := first [ exact cursor_ctor_art | exact get_string_art | exact read_next_art | d ].
Lemma chain_as : HNKC.harness_chainA art_L ar HI IC LibTopCA.LTCA.PC_LIB 0 false.   Proof. eapply HarnessAsCA.harness_as_ok; hd. Qed.
Lemma chain_al : HNKC.harness_chainA art_L ar HI IC LibTopCA.LTCA.PC_LIB 0 true.    Proof. eapply HarnessAlCA.harness_al_ok; hd. Qed.
Lemma chain_bs : HNKC.harness_chainA art_L ar HI IC LibTopCA.LTCA.PC_LIB 16 false.  Proof. eapply HarnessBsCA.harness_bs_ok; hd. Qed.
Lemma chain_bl : HNKC.harness_chainA art_L ar HI IC LibTopCA.LTCA.PC_LIB 16 true.   Proof. eapply HarnessBlCA.harness_bl_ok; hd. Qed.

Theorem lib_specA_c_art : PMCSA.lib_specA_c art_L ar HI IC ASMC.LayC8.
Proof. exact (LibTopCA.LTCA.lib_specA_c_ok art_L ar art_C HI HIok0 TPV0 chain_as chain_al chain_bs chain_bl ASMC.LayC8 eq_refl eq_refl eq_refl). Qed.
End Inst.

Section Top.

Lemma libtop : forall (ar : asan_run) (HI : asan_iface),
  as0_icpt_layout PmCasanFinal.art_IL -> pm_icpt_layout_x PmCasanFinal.art_ILX ->
  pm_asan_iface_ok art_L art_LX ar art_C PmCasanFinal.cfg0 HI ->
  pm_aicpt_ok art_L ar PmCasanFinal.art_IL PmCasanFinal.art_ILX PmCasanFinal.cfg0 HI (aannotate_spec art_L ar PmCasanFinal.cfg0 HI (iclx_annotate PmCasanFinal.art_ILX) 4096) ->
  afree_null_spec art_L ar PmCasanFinal.cfg0 HI ->
  PMCSA.lib_specA_c (SCFG_P := MkScfgP PmCasanFinal.cfg0) art_L ar HI PMLA.C_casan ASMC.LayC8.
Proof. intros ar HI ILok ILXok HIok ICok FN. eapply lib_specA_c_art; eassumption. Qed.
End Top.
End PmCasanLibTop.
