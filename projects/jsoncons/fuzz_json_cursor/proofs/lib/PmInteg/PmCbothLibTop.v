(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs PmCurSpecsA PmFloatCSpecsA PmFloatCWD HnSpecCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9IcptLayout Pm9L5DefsA Pm9ArtFsInv Pm9ArtIfaceInst Pm9ArtIfaceInstX PmLibAssemblyCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require PmCbothFinal PmLibGlueCB Pm9StrtodG DecstrGCB Pm9FloatLayout.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FloatCB Require SnprintfCpsB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutRtCpsA.

From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require TopSpecsCB HnKitCB SetEc2CB ConvEcCB StrInit2CB RChunkCurCB ReadNextCB CursorMainCB CursorCtorCB CStrCB GetLitCB GetStrCB FromIntCB FromInt64CB
  HarnessAsCB HarnessAlCB HarnessBsCB HarnessBlCB LibTopCB StrPushShortCB DumpBufCB PrettifyCB DtoaFalseCB DtoaTrueCB WriteDoubleCB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PmCurSpecsBLocal.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PmCbothLibTop.
Abbreviation IC := PMLA.C_cboth.
Module G := PmLibGlueCB.GLCB.

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
Let ISH : rt_img_shadow art_L IL HI := pic_img_shadow _ _ _ _ _ _ _ ICok.
Let RTG : rt_globals IL HI := pic_globals _ _ _ _ _ _ _ ICok.
Let STRLEN : astrlen_spec art_L ar IL scfg HI := pic_strlen _ _ _ _ _ _ _ ICok.
Lemma FOOTC2 : forall a, PMLA.in_foot IC a -> ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a.  Proof. exact G.FOOTC2. Qed.
Lemma MEMSET_LIBC : CRC.amemset_spec_at art_L ar HI 0x7f228.  Proof. eapply G.MEMSET_LIBC; eassumption. Qed.
Lemma SETSHF5 : aset_shadow_spec art_L ar scfg HI 0x82eac 245 256.  Proof. eapply G.SETSHF5; eassumption. Qed.
Lemma SETSH00 : aset_shadow_spec art_L ar scfg HI 0x82da4 0 256.  Proof. eapply G.SETSH00; eassumption. Qed.
Lemma SETSHF8 : aset_shadow_spec art_L ar scfg HI 0x82ec4 248 256.  Proof. eapply G.SETSHF8; eassumption. Qed.
Lemma SF5 : PmHeapIfaceA.astack_free_spec art_L ar scfg HI 0x65888 0x103a8 5.  Proof. eapply G.SF5; eassumption. Qed.
Lemma PATR : 0x10000 <= 0x103a8 /\ 0x103a8 + 8 <= 0x156000.  Proof. lia. Qed.
Lemma TPV0 : hl_tp art_L = 6888848.  Proof. exact ASMCB.art_tp. Qed.
Lemma TPV : hl_tp art_L - 164 = 6888684.  Proof. rewrite TPV0. reflexivity. Qed.
Lemma MEMMOVE_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7f22c false.  Proof. eapply G.MEMMOVE_LIBC; eassumption. Qed.
Lemma MEMCPY_LIBC : amemcpy_spec_at art_L ar scfg HI 0x7f230 false.  Proof. eapply G.MEMCPY_LIBC; eassumption. Qed.
Let RSD : rt_shadow_defined HI := pic_shadow_defined _ _ _ _ _ _ _ ICok.
Lemma incl_of_b : forall (l1 l2 : list (Z * Z * Z)),
  forallb (fun x => existsb (fun y => (fst (fst x) =? fst (fst y)) && (snd (fst x) =? snd (fst y)) && (snd x =? snd y)) l2) l1 = true -> incl l1 l2.
Proof.
  intros l1 l2 H x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply existsb_exists in H as (y & Hy & E).
  apply andb_prop in E as (E & E3). apply andb_prop in E as (E1 & E2). apply Z.eqb_eq in E1, E2, E3.
  destruct x as [[a b] c], y as [[a' b'] c']. cbn in *. subst. exact Hy.
Qed.

Lemma strinit_art : PMSA.strinit_specA art_L ar HI 720088.                          Proof. eapply G.strinit_art; eassumption. Qed.
Lemma iss_ctorX_art : HnKitCB.HNK.iss_ctor_specX art_L ar HI IC 720448.             Proof. eapply G.iss_ctorX_art; eassumption. Qed.
Lemma system_category_art : PMSA.system_category_specA art_L ar HI IC 1007612.      Proof. eapply G.system_category_art; eassumption. Qed.
Lemma parser_dtor_art : PMSA.parser_dtor_specA art_L ar HI IC 726328.                Proof. eapply G.parser_dtor_art; eassumption. Qed.
Lemma source_dtor_art : PMSA.source_dtor_specA art_L ar HI IC 728272.                Proof. eapply G.source_dtor_art; eassumption. Qed.
Lemma locale_dtor_art : PMSA.locale_dtor_specA art_L ar HI IC 1161820.              Proof. eapply G.locale_dtor_art; eassumption. Qed.
Lemma locale_ctor_later_art : PMSA.locale_ctor_later_specA art_L ar HI IC 1161604.  Proof. eapply G.locale_ctor_later_art; eassumption. Qed.
Lemma opdel_art : PMSA.opdel_specA art_L ar HI 980676.                               Proof. eapply G.opdel_art; eassumption. Qed.
Lemma opnew_art : PMSA.opnew_specA art_L ar HI 1363704.                              Proof. eapply G.opnew_art; eassumption. Qed.
Lemma str_reserve_art : PMSA.str_reserve_specA art_L ar HI 989296.                   Proof. eapply G.str_reserve_art; eassumption. Qed.
Lemma vec_reserve_art : PMSA.vec_reserve_specA art_L ar HI 829676.                   Proof. eapply G.vec_reserve_art; eassumption. Qed.
Lemma vec_push_art : PMSA.vec_push_specA art_L ar HI 807908.                         Proof. eapply G.vec_push_art; eassumption. Qed.
Lemma guard_acquire_art : PMSA.guard_acquire_specA art_L ar HI 863640.               Proof. eapply G.guard_acquire_art; eassumption. Qed.
Lemma guard_release_art : PMSA.guard_release_specA art_L ar HI 863720.               Proof. eapply G.guard_release_art; eassumption. Qed.
Lemma set_ec_art : PMSA.set_ec_specA art_L ar HI IC 749196.                          Proof. eapply G.set_ec_art; eassumption. Qed.
Lemma parse_some_art : PMSA.parse_some_specA art_L ar HI IC 751580.                  Proof. eapply G.parse_some_art; eassumption. Qed.
Lemma detect_json_art : TopSpecsCB.TPSA.detect_json_specA art_L ar HI IC 750032.     Proof. eapply G.detect_json_art; eassumption. Qed.
Lemma xsgetn_art : TopSpecsCB.TPSA.xsgetn_specA art_L ar HI IC 1012508.              Proof. eapply G.xsgetn_art; eassumption. Qed.

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
  | |- PMSA.strinit_specA _ _ _ ?pc => first [ exact strinit_art | exact (StrInit2CB.strinit2_ok _ _ _ _ HIok0 LAY FPM opnew_art) ]
  | |- HnKitCB.HNK.iss_ctor_specX _ _ _ _ _ => exact iss_ctorX_art
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
  | |- TopSpecsCB.TPSA.detect_json_specA _ _ _ _ _ => exact detect_json_art
  | |- TopSpecsCB.TPSA.xsgetn_specA _ _ _ _ _ => exact xsgetn_art
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
  | |- hl_stack_malloc _ _ = _ => first [ exact ASMCB.art_sm0 | exact ASMCB.art_sm1 | exact ASMCB.art_sm2 | exact ASMCB.art_sm3 | exact ASMCB.art_sm4 | exact ASMCB.art_sm5 ]
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
  | exact Pm9FloatLayout.art_float
  | rows
  | facts
  | assumption
  | reflexivity ].

Lemma set_ec2_art : PMCSA.set_ec2_specA art_L ar HI IC 827556.            Proof. eapply SetEc2CB.set_ec2_ok; d. Qed.
Lemma conv_ec_art : PMCSA.conv_ec_specA art_L ar HI IC 729476.            Proof. eapply ConvEcCB.conv_ec_ok; d. Qed.
Lemma strinit2_art : PMSA.strinit_specA art_L ar HI 849628.                Proof. eapply StrInit2CB.strinit2_ok; d. Qed.
Lemma read_chunk_c_art : PMCSA.read_chunk_c_specA art_L ar HI IC 748928.  Proof. eapply RChunkCurCB.read_chunk_c_ok; d. Qed.
Lemma read_next_art : PMCSA.read_next_specA art_L ar HI IC 737356.
Proof. eapply ReadNextCB.read_next_ok; first [ exact read_chunk_c_art | d ]. Qed.
Lemma cursor_main_art : PMCSB.cursor_main_specB art_L ar HI IC 821724 1370328 1370368 1370488.
Proof. eapply CursorMainCB.cursor_main_ok; first [ exact read_next_art | exact set_ec2_art | d ]. Qed.
Lemma cursor_ctor_art : PMCSA.cursor_ctor_specA art_L ar HI IC 721120.
Proof. eapply CursorCtorCB.cursor_ctor_ok; first [ exact cursor_main_art | d ]. Qed.

Lemma cstr_art : PMCSB.cstr_ctor_specB art_L ar HI IC 863168.             Proof. eapply CStrCB.cstr_ok; d. Qed.
Lemma from_integer_u64_art : PMFCA.from_integer_u64_specA art_L ar HI IC 843204.  Proof. eapply FromIntCB.from_integer_u64_ok; d. Qed.
Lemma from_integer_i64_art : PMFCA.from_integer_i64_specA art_L ar HI IC 844828.  Proof. eapply FromInt64CB.from_integer_i64_ok; d. Qed.

Lemma push_short_art : PMFCA.str_push_back_short_specA art_L ar HI 990424.   Proof. eapply StrPushShortCB.str_push_back_short_ok; d. Qed.
Lemma push_l48_art : PMFCA.str_push_back_l48_specA art_L ar HI 990424.       Proof. eapply StrPushShortCB.str_push_back_l48_ok; d. Qed.
Ltac dw := first [ exact push_short_art | exact push_l48_art | d ].
Lemma dump_buffer_art : PMFCA.dump_buffer_specA art_L ar HI 851872.          Proof. eapply DumpBufCB.dump_buffer_ok; dw. Qed.
Lemma prettify_art : PMFCA.prettify_specA art_L ar HI 855636.                Proof. eapply PrettifyCB.prettify_ok; dw. Qed.
Lemma strtod_g_art : PMFCA.strtod_g_specA art_L ar HI IC 1333096.            Proof. eapply Pm9StrtodG.STGA.strtod_g_okA; d. Qed.
Lemma decstr_g_art : PMFCA.decstr_to_double_g_specA art_L ar HI IC 805428.   Proof. eapply DecstrGCB.decstr_g_ok; first [ exact strtod_g_art | d ]. Qed.
Lemma snprintf_art : PMFCA.snprintf_g_specA art_L ar HI IC SnprintfCpsB.PC_SNPRINTF_cboth SnprintfCpsB.FMT_ADDR.  Proof. eapply SnprintfCpsB.snprintf_g_okB; d. Qed.
Lemma dtoa_false_art : PMFCA.dtoa_false_specA art_L ar HI IC 862208.
Proof. eapply DtoaFalseCB.dtoa_false_ok; first [ exact snprintf_art | exact decstr_g_art | exact dump_buffer_art | d ]. Qed.
Lemma dtoa_true_art : PMFCA.dtoa_true_specA art_L ar HI IC 861312.
Proof. eapply DtoaTrueCB.dtoa_true_ok; first [ exact dtoa_false_art | exact prettify_art | d ]. Qed.
Lemma write_double_art : PMFCW.write_double_specW art_L ar HI IC 846852.
Proof. eapply WriteDoubleCB.write_double_ok; first [ exact dtoa_true_art | d ]. Qed.
Lemma get_string_art : PMCSA.get_string_specA art_L ar HI IC 841728.
Proof.
  eapply GetStrCB.get_string_ok;
    first [ exact conv_ec_art | exact cstr_art | exact strinit2_art | exact from_integer_i64_art | exact from_integer_u64_art | exact write_double_art | d ].
Qed.

Ltac hd := first [ exact cursor_ctor_art | exact get_string_art | exact read_next_art | d ].
Lemma chain_as : HNKC.harness_chainA art_L ar HI IC LibTopCB.LTCA.PC_LIB 0 false.   Proof. eapply HarnessAsCB.harness_as_ok; hd. Qed.
Lemma chain_al : HNKC.harness_chainA art_L ar HI IC LibTopCB.LTCA.PC_LIB 0 true.    Proof. eapply HarnessAlCB.harness_al_ok; hd. Qed.
Lemma chain_bs : HNKC.harness_chainA art_L ar HI IC LibTopCB.LTCA.PC_LIB 16 false.  Proof. eapply HarnessBsCB.harness_bs_ok; hd. Qed.
Lemma chain_bl : HNKC.harness_chainA art_L ar HI IC LibTopCB.LTCA.PC_LIB 16 true.   Proof. eapply HarnessBlCB.harness_bl_ok; hd. Qed.

Theorem lib_specA_c_art : PMCSA.lib_specA_c art_L ar HI IC ASMCB.LayC9.
Proof. exact (LibTopCB.LTCA.lib_specA_c_ok art_L ar art_C HI HIok0 TPV0 chain_as chain_al chain_bs chain_bl ASMCB.LayC9 eq_refl eq_refl eq_refl). Qed.
End Inst.

Section Top.

Lemma libtop : forall (ar : asan_run) (HI : asan_iface),
  as0_icpt_layout PmCbothFinal.art_IL -> pm_icpt_layout_x PmCbothFinal.art_ILX ->
  pm_asan_iface_ok art_L art_LX ar art_C PmCbothFinal.cfg0 HI ->
  pm_aicpt_ok art_L ar PmCbothFinal.art_IL PmCbothFinal.art_ILX PmCbothFinal.cfg0 HI (aannotate_spec art_L ar PmCbothFinal.cfg0 HI (iclx_annotate PmCbothFinal.art_ILX) 4096) ->
  afree_null_spec art_L ar PmCbothFinal.cfg0 HI ->
  PMCSA.lib_specA_c (SCFG_P := MkScfgP PmCbothFinal.cfg0) art_L ar HI PMLA.C_cboth ASMCB.LayC9.
Proof. intros ar HI ILok ILXok HIok ICok FN. eapply lib_specA_c_art; eassumption. Qed.
End Top.
End PmCbothLibTop.
