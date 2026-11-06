(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibSpecs PmEncSpecs PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5IcptLayout Pm5L5DefsA Pm5ArtFsInv Pm5ArtIfaceInst Pm5ArtIfaceInstX PmLibAssemblyXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIfaceN Pm5ArtIfaceInstN OpNewXBNP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module IFXB.
Abbreviation IC := PMLA.C_xboth.

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

Lemma HIok0 : PmHeapIfaceA.asan_iface_ok art_L ar art_C scfg HI.  Proof. exact (pio_base _ _ _ _ _ _ HIok). Qed.
Definition LAY := ASMXB.art_lay.
Definition FPM := ASMXB.art_fpm.
Definition FOOTC := ASMXB.art_footc.
Definition FOOTC2 := ASMXB.art_footc2.
Definition FOOTXC := ASMXB.art_footxc.
Definition FOOTXC2 := ASMXB.art_footxc2.      (* [comment removed for export] *)
Lemma TPV : hl_tp art_L = 6953104.  Proof. reflexivity. Qed.
Lemma ISH : rt_img_shadow art_L IL HI.  Proof. exact (pic_img_shadow _ _ _ _ _ _ _ ICok). Qed.
Lemma ANN : aannotate_spec art_L ar scfg HI 542968 4096.
Proof. rewrite <- (aiclx_annotate ILX ILXok). exact (pic_annotate _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMSET_LIBC : CRC.amemset_spec_at art_L ar HI 0x80b04.
Proof.
  rewrite <- (aiclx_memset ILX ILXok).
  intros fx R M model LB FF LK cr A dst c n Kt. exact (pic_memset_libc _ _ _ _ _ _ _ ICok fx R M model LB FF LK cr A dst c n Kt).
Qed.
Lemma MEMCPY_LIBC : amemcpy_spec_at art_L ar scfg HI 0x80b0c false.
Proof. rewrite <- (aicl_memcpy IL ILok). exact (pic_memcpy_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMMOVE_LIBC : amemcpy_spec_at art_L ar scfg HI 0x80b08 false.
Proof. rewrite <- (aicl_memmove IL ILok). exact (pic_memmove_libc _ _ _ _ _ _ _ ICok). Qed.
Lemma MEMCMP_TU : amemcmp_spec_at art_L ar scfg HI 0x6c200 8192.
Proof. rewrite <- (aiclx_memcmp ILX ILXok), <- (aiclx_scr_memcmp ILX ILXok). exact (pic_memcmp _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF5 : aset_shadow_spec art_L ar scfg HI 542600 245 256.
Proof. rewrite <- (aiclx_setshf5 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf5 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSH00 : aset_shadow_spec art_L ar scfg HI 542336 0 256.
Proof. rewrite <- (aiclx_setsh00 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setsh00 _ _ _ _ _ _ _ ICok). Qed.
Lemma SETSHF8 : aset_shadow_spec art_L ar scfg HI 542624 248 256.
Proof. rewrite <- (aiclx_setshf8 ILX ILXok), <- (aiclx_scr_setsh ILX ILXok). exact (pic_setshf8 _ _ _ _ _ _ _ ICok). Qed.

Definition PAT : Z := 0x103a8.
Lemma PATR : 65536 <= PAT /\ PAT + 8 <= 1466368.  Proof. unfold PAT. lia. Qed.
Lemma SF5 : PmHeapIfaceA.astack_free_spec art_L ar scfg HI 422244 PAT 5.
Proof. unfold PAT. rewrite <- ASMXB.art_sfree5, <- ASMXB.art_sfree_pat. exact (pio_stack_free5 _ _ _ _ _ _ HIok). Qed.

Ltac poi := rewrite (aicl_poison IL ILok); unfold ART_POISON; cbv -[Z.le Z.lt Z.add fst snd];
            repeat first [ apply Forall_nil | apply Forall_cons | (cbn [fst snd]; lia) ].
Lemma POI_VTT : Forall (fun r : Z * Z => 1435080 + 16 <= fst r \/ snd r <= 1435080) (icl_poison IL).  Proof. poi. Qed.
Lemma POI_VBO : Forall (fun r : Z * Z => 1435000 + 8 <= fst r \/ snd r <= 1435000) (icl_poison IL).  Proof. poi. Qed.
Lemma POI_ISS : Forall (fun r : Z * Z => 1450352 + 8 <= fst r \/ snd r <= 1450352) (icl_poison IL).  Proof. poi. Qed.
Lemma POI_HN : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) [1450432; 1450456; 1450352]) (icl_poison IL).
Proof. rewrite (aicl_poison IL ILok); unfold ART_POISON. repeat first [ apply Forall_nil | apply Forall_cons ]; cbn [fst snd]; lia. Qed.
(* [comment removed for export] *)
Definition ISHRG5 : list (Z * Z) := [(1459120, 8); (84888, 8); (1435080, 8); (1435088, 8); (1435000, 8)].
Lemma POI_EC5 : Forall (fun r : Z * Z => Forall (fun an : Z * Z => fst an + snd an <= fst r \/ snd r <= fst an) ISHRG5) (icl_poison IL).
Proof. unfold ISHRG5. rewrite (aicl_poison IL ILok); unfold ART_POISON. repeat first [ apply Forall_nil | apply Forall_cons ]; cbn [fst snd]; lia. Qed.
(* [comment removed for export] *)
Lemma img_aacc_of_global : forall q n p m, In (q, n) (icl_globals IL) -> q mod 8 = 0 -> 0 <= q -> q <= p -> p + m <= q + n -> PMESA.img_aacc HI p m.
Proof.
  intros q n p m Hin Hal Hq Hp Hm LB FF LK cr A M V RI.
  pose proof (pic_globals _ _ _ _ _ _ _ ICok LB FF LK cr A M V RI) as G.
  rewrite Forall_forall in G. specialize (G (q, n) Hin). cbn [fst snd] in G. destruct G as [SB _].
  exact (CRC.aacc_blk M q n p m SB Hal Hq Hp Hm).
Qed.
Lemma img_aacc_of_ish : forall p m, hl_img_lo art_L <= p -> p + m <= hl_img_hi art_L -> 0 < m ->
  Forall (fun r : Z * Z => p + m <= fst r \/ snd r <= p) (icl_poison IL) -> PMESA.img_aacc HI p m.
Proof.
  intros p m Hlo Hhi Hm HP LB FF LK cr A M V RI a Ha. left.
  destruct (pic_img_shadow _ _ _ _ _ _ _ ICok LB FF LK cr A M V RI p m Hlo Hhi Hm HP) as [Z0 _].
  apply Z0. unfold in_shadow_of, S. split; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia].
Qed.
Ltac accg q n := apply (img_aacc_of_global q n); [rewrite (aicl_globals IL ILok); unfold ART_GLOBALS; cbv; tauto | reflexivity | lia | lia | lia].
Ltac acci := apply img_aacc_of_ish; [cbn; lia | cbn; lia | lia | poi].
(* [comment removed for export] *)
Lemma RTG : rt_globals IL HI.  Proof. exact (pic_globals _ _ _ _ _ _ _ ICok). Qed.
Definition ECGLOBS : list (Z * Z) := [(1436768, 24); (1436832, 24); (166624, 24); (166688, 24)].
Lemma GLIN : Forall (fun g : Z * Z => In g (icl_globals IL)) ECGLOBS.
Proof. unfold ECGLOBS. rewrite (aicl_globals IL ILok); unfold ART_GLOBALS. repeat first [ apply Forall_nil | apply Forall_cons ]; cbv; tauto. Qed.
(* [comment removed for export] *)
Lemma ACC_NULL : PMESA.img_aacc HI 154688 4.  Proof. accg 154688 5. Qed.
Lemma ACC_TRUE : PMESA.img_aacc HI 165440 4.  Proof. accg 165440 5. Qed.
Lemma ACC_FALSE : PMESA.img_aacc HI 165472 5.  Proof. accg 165472 6. Qed.
(* [comment removed for export] *)
Lemma ACC_JT1 : PMESA.img_aacc HI 166624 24.  Proof. accg 166624 24. Qed.
Lemma ACC_JT2 : PMESA.img_aacc HI 166688 24.  Proof. accg 166688 24. Qed.
Lemma ACC_OB1 : PMESA.img_aacc HI 1436768 24.  Proof. accg 1436768 24. Qed.
Lemma ACC_OB2 : PMESA.img_aacc HI 1436832 24.  Proof. accg 1436832 24. Qed.
(* [comment removed for export] *)
Lemma ACC_COLON : PMESA.img_aacc HI 150388 2.  Proof. acci. Qed.
Lemma ACC_COMMA : PMESA.img_aacc HI 150396 2.  Proof. acci. Qed.
Lemma ACC_OBRACE : PMESA.img_aacc HI 150408 1.  Proof. acci. Qed.
Lemma ACC_CBRACE : PMESA.img_aacc HI 150409 1.  Proof. acci. Qed.
Lemma ACC_OBRACKET : PMESA.img_aacc HI 150414 1.  Proof. acci. Qed.
Lemma ACC_CBRACKET : PMESA.img_aacc HI 150415 1.  Proof. acci. Qed.
(* [comment removed for export] *)
Lemma POI_TC : Forall (fun r : Z * Z => 151792 + 288 <= fst r \/ snd r <= 151792) (icl_poison IL).  Proof. poi. Qed.
Lemma CL40X : ASMXB.CLX <= 2 ^ 40.  Proof. unfold ASMXB.CLX. lia. Qed.   (* [comment removed for export] *)
Lemma CLOKX : 8 <= ASMXB.CLX /\ 2 * ASMXB.CLX + 8 <= HeapIfaceN.NB /\ 32768 <= HeapIfaceN.NB /\ HeapIfaceN.NB <= 2 ^ 47.   (* [comment removed for export] *)
Proof. unfold ASMXB.CLX, HeapIfaceN.NB. lia. Qed.
(* [comment removed for export] *)
Lemma SM0 : hl_stack_malloc art_L 0 = 0x66740.  Proof. reflexivity. Qed.
Lemma SM1 : hl_stack_malloc art_L 1 = 0x668b4.  Proof. reflexivity. Qed.
Lemma SM2 : hl_stack_malloc art_L 2 = 0x66a44.  Proof. reflexivity. Qed.
Lemma SM3 : hl_stack_malloc art_L 3 = 0x66be0.  Proof. reflexivity. Qed.
Lemma SM4 : hl_stack_malloc art_L 4 = 0x66d8c.  Proof. reflexivity. Qed.
Lemma SM5 : hl_stack_malloc art_L 5 = 0x66f58.  Proof. reflexivity. Qed.
Lemma CXA_PC : iclx_cxa_atexit ILX = 443080.  Proof. exact (aiclx_cxa_atexit ILX ILXok). Qed.
Lemma CXA_SCR : 0 <= iclx_scr_cxa ILX <= 512.  Proof. rewrite (aiclx_scr_cxa ILX ILXok). lia. Qed.
Lemma CXA_TAB : iclx_atexit_tab ILX = PMLA.ATEXIT_TAB IC.  Proof. exact (aiclx_atexit_tab ILX ILXok). Qed.
Lemma CXA_AT : iclx_atcxa ILX = PMLA.ATCXA_HANDLER IC.  Proof. exact (aiclx_atcxa ILX ILXok). Qed.
Lemma CXA_NL : iclx_need_locks ILX = PMLA.NEED_LOCKS IC.  Proof. exact (aiclx_need_locks ILX ILXok). Qed.
Definition VTSLOTS : list Z := [1435224; 1435232; 1435240; 1435248; 1435256; 1435264; 1435280; 1435288; 1435296; 1435304; 1435312; 1435320;
  1436056; 1436216; 1436224; 1436240; 1436512; 1436520; 1436528; 1436536; 1436552; 1436568; 1436576; 1436584; 1436592; 1436600; 1436608; 1450200; 1450352; 1450432; 1450456].
Lemma POI_VT : Forall (fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) VTSLOTS) (icl_poison IL).
Proof. unfold VTSLOTS. rewrite (aicl_poison IL ILok); unfold ART_POISON. repeat first [ apply Forall_nil | apply Forall_cons ]; cbn [fst snd]; lia. Qed.
Lemma POI_IOS32 : Forall (fun r : Z * Z => 1450472 <= fst r \/ snd r <= 1450440) (icl_poison IL).  Proof. poi. Qed.
Lemma POI_BOM : Forall (fun r : Z * Z => 166030 <= fst r \/ snd r <= 166014) (icl_poison IL).  Proof. poi. Qed.
(* [comment removed for export] *)
Lemma POI_TAB : Forall (fun r : Z * Z => 166144 + 256 <= fst r \/ snd r <= 166144) (icl_poison IL).  Proof. poi. Qed.
(* [comment removed for export] *)
Lemma POI_MS : Forall (fun r : Z * Z => 0x6a07e8 <= fst r \/ snd r <= 0x6a06f8) (icl_poison IL).  Proof. poi. Qed.
Lemma POI_RO : Forall (fun r : Z * Z => 0x30868 <= fst r \/ snd r <= 0x30838) (icl_poison IL).  Proof. poi. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FLA : hl_tp art_L = 0x6a1890 /\
  forall a, (0x6a1890 - 164 <= a < 0x6a1890 - 164 + 4 \/ 0x6c18d0 <= a < 0x6c18d0 + 8) ->
    hl_img_lo art_L <= a < hl_img_hi art_L /\ ~ hl_rt_static art_L a /\ ~ hl_rt_ro art_L a /\ (a < 0x10000 \/ 0x166000 <= a).
Proof.
  split; [reflexivity|]. intros a Ha. cbn [art_L hl_img_lo hl_img_hi hl_rt_static hl_rt_ro hl_tp]. unfold art_static, art_ro. lia.
Qed.
Lemma ERRNO_NS : forall a, 6952940 <= a < 6952940 + 4 -> ~ hl_rt_static art_L a.
Proof. intros a Ha. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.
(* [comment removed for export] *)
Lemma GLT : In (0x25d40, 8 * 687) (icl_globals IL).  Proof. rewrite (aicl_globals IL ILok); unfold ART_GLOBALS. cbv. tauto. Qed.
Lemma GLE : In (0x27800, 4 * 687) (icl_globals IL).  Proof. rewrite (aicl_globals IL ILok); unfold ART_GLOBALS. cbv. tauto. Qed.
Lemma ILG_FMT : In (0x25d20, 6) (icl_globals IL).  Proof. rewrite (aicl_globals IL ILok); unfold ART_GLOBALS. cbv. tauto. Qed.
Lemma RSD : rt_shadow_defined HI.  Proof. exact (pic_shadow_defined _ _ _ _ _ _ _ ICok). Qed.
Lemma POI_SNP : Forall (fun r : Z * Z => 147584 <= fst r \/ snd r <= 77760) (icl_poison IL).  Proof. poi. Qed.
(* [comment removed for export] *)
Section InstN.
Hypothesis INok : Pm5ArtIfaceInstN.pm_instN art_L ar IL scfg HI.
Lemma OPNEWX : PMESA.opnew_x_specA art_L ar HI HeapIfaceN.NB 1429232.
Proof. exact (OpNewXBNP.opnewN_x_ok art_L ar art_C HI HIok0 LAY FPM (Pm5ArtIfaceInstN.pin_mallocN _ _ _ _ _ INok)). Qed.
Lemma MEMCPY_X : PMESA.amemcpy_x_spec_at art_L ar HI HeapIfaceN.NB 527116 false.
Proof.
  pose proof (Pm5ArtIfaceInstN.pin_memcpy_libcN _ _ _ _ _ INok) as MC. unfold HeapIfaceN.amemcpy_libc_specN in MC. rewrite (aicl_memcpy IL ILok) in MC. exact MC.
Qed.
Lemma MEMMOVE_X : PMESA.amemcpy_x_spec_at art_L ar HI HeapIfaceN.NB 527112 false.
Proof.
  pose proof (Pm5ArtIfaceInstN.pin_memmove_libcN _ _ _ _ _ INok) as MC. unfold HeapIfaceN.amemmove_libc_specN in MC. rewrite (aicl_memmove IL ILok) in MC. exact MC.
Qed.
End InstN.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma POI_CV : Forall (fun r : Z * Z => 166496 + 8 <= fst r \/ snd r <= 166496) (icl_poison IL).  Proof. poi. Qed.
End Inst.
End IFXB.
