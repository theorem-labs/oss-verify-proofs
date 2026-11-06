(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the program side, composed at the
   pinned image (the role of plugin-hostd/fuzz_command's lib/B/Prog/CmdProgClosed.v, origin/ossv/recipes
   501c0d516c69; the twin of image A's lib/A/Prog/SegProgClosed.v, commit 6f7a1561a103): the contract `<F>_contract`
   (lib/B/Prog/<F>_c.v) of each of image B's 36 program functions at image B's instance SegImg.PB_seg (segments
   tfibsegs), the sink head YE2k.tfib_sink_head and an allocator record B with image B's symbol record
   (YF0m.SegBSyms B), at every run ceiling and FP state, from each function's walk (its group's theorem, applied to
   its callees' closures, to the listing's record facts and to the runtime rows).
   The walks state entries and call targets as listing terms under `Context {PI : PAImg seg_listing}`: here
   PI := PB_seg, and the top is rewritten to SegInstB's A_LLVMFuzzerTestOneInput_A by
   SegInstPB.pb_entry_LLVMFuzzerTestOneInput.
   Every piece is instantiated; the only Section premises left are the record facts HB and HD, which the top
   (lib/B/SegTopB.v) fills with the core's record lib/B/YD2l.v SegB:
   - all 36 walks: G1 (LLVMFuzzerTestOneInput's walk), G2 (lib/B/Prog/SegG2.v: reac_box_catalogue,
     fuzz_catalogue_row, ieq, reac_box_catalogue_by_token, m_find, strip, fold, m_refuse, m_file), G3 (trim,
     refuse, cross_check, reac_segconf_parse_file, reac_segconf_parse) and G4 + G5 (lib/B/Prog/SegG45.v, 21 walks);
   - the record facts by the listing's lemmas (SegRecRest, SegRecImg, SegRecRo, SegRecBase, SegRecCells) from
     SegBSyms B, and the three listing facts (memchr's word-constant window, LLVMFuzzerTestOneInput's longl facts) by
     lib/B/Prog/SegRecLtoi.v;
   - the core's runtime rows by their proved contracts: checked memset / memcpy, side-stack classes 0 / 1 / 3 / 5,
     __asan_stack_free_5 and the three shadow fills (lib/B/Rt/RtClosed.v); the fake-stack bound from the listing's
     image cover and the layout (h_snp_fake below; fuzz_command's lib/B/Rt/RtPFDog.v pa_fake_above_img); the
     allocator rows amalloc04 / afree04 by image B's malloc chain (lib/B/YF0w.v) and free closer (lib/B/YF0q.v) at
     the record's hash HD;
   - the interceptor rows by the interceptor layer's closings (lib/B/Rt/SegRtClosed.v, bcmp included), calloc at its
     own window RtLCalloc.SEG_CALLOC_CSTK.
   The allocator record is a Section variable B with its symbol record HB: the core's image-B record lib/B/YD2l.v
   SegB / SegB_syms (fuzz_command's lib/B/YD2l.v CmdB) instantiates it at the top (lib/B/SegTopB.v).
   proves no function (kind: merge; the composition of the walk closures). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d YCbq YC5d YB1v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YF0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YG0t YF0m YF0q YF0w YE2k YCbp SegInstPB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable SegSyms SegList SegPa SegPaLib PaLibF SegObj SegGlob SegImg SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require
SegRecBase SegRecRest SegRecRo SegRecCells SegRecImg SegRecLtoi m_file_memchr reac_segconf_declared_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require
RtString RtSeg RtPFSeg RtPFCmd RtAPI MemchrDef RtFormat RtStack RtShadow RtSegCalloc RtClosed SegRtClosed
RtLCalloc SegRtPC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_inst
  trim_c refuse_c cross_check_c reac_segconf_parse_file_c reac_segconf_parse_c
  reac_segconf_find_c reac_segconf_init_c reac_segconf_role_file_c reac_segconf_role_c reac_segconf_ignore_file_c
  reac_segconf_ignored_c reac_segconf_model_c check_absent_c check_segments_c check_role_c check_model_c
  check_ignore_c check_provenance_c check_refusals_c check_address_c check_knock_refused_c check_declared_c name_ok_c
  reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c
  fuzz_catalogue_row_c reac_box_catalogue_c reac_box_catalogue_by_token_c ieq_c m_find_c m_refuse_c strip_c fold_c
  m_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegG45 SegG2
  trim refuse cross_check reac_segconf_parse_file reac_segconf_parse LLVMFuzzerTestOneInput.
Import ListNotations.
Local Open Scope Z_scope.

Create HintDb gpc.

Section closed. Context {rc : YM05.RunCeil}.
#[local] Existing Instance YE2k.tfib_sink_head | 0.
#[local] Notation BASE := (@pa_val _ seg_listing PB_seg A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PB_seg s).

(* the allocator record and image B's symbol record (lib/B/YF0m.v); the core's YD2l-twin record instantiates B *)
Variable B : asyms.
Hypothesis HB : YF0m.SegBSyms B.
(* the record's hash is the model's (YD2l.SegB: as_dhash := tfib_dhash, so eq_refl at the top) *)
Hypothesis HD : forall t, as_dhash B t = YF0p.tfib_dhash t.

(* ---- the record and listing facts, by the listing's lemmas ------------------------------------------------ *)
Lemma seg_IMG : SegRecBase.seg_img_facts tfibsegs B.
Proof. exact (SegRecImg.seg_img_facts_tfib B HB). Qed.
Lemma seg_ERRNO : errno_rom tfibsegs B.
Proof. exact (SegRecBase.cif_errno _ _ seg_IMG). Qed.
#[local] Instance seg_ro_below : ro_below_ofl tfibsegs RLO_A RHI_A.
Proof. eapply SegRecRo.ROB; solve [exact HB | exact seg_IMG | exact (YG0q.AR_laws_ok _ _)]. Qed.
(* the stack-protector cells at every AR state: the .got word gotwA holds guardA (the record pins it,
   SegRecCells.crf_guard_got_chk) and the guard's 8 bytes have image bytes (the record's cif_guard_rom); the image-B
   twin of image A's SegRecCells.seg_ssp *)
Lemma seg_sspx : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  sa_ssp (aview tfibsegs (w_H W) mem) gotwA guardA.
Proof.
intros ly S W mem md HAR. split.
- assert (C : SegRecBase.seg_word_b gotwA guardA = true) by exact SegRecCells.crf_guard_got_chk.
  eapply SegRecBase.seg_word_chk; eauto using YG0q.AR_laws_ok.
- apply SegRecBase.crf_rdword_some. intros k Hk. apply SegRecBase.crf_rom_view_some.
  apply (SegRecBase.cif_guard_rom _ _ seg_IMG). unfold guardA. lia.
Qed.
Lemma seg_dc_ssp : reac_segconf_declared_d.dc_sspP (PI := PB_seg) B gotwA guardA.
Proof. exact seg_sspx. Qed.
(* LLVMFuzzerTestOneInput's longl is not a read-only byte (the record's cif_prog_not_ro; ltoi_PG longlA is seg_PG) *)
Lemma seg_hpg_ro : forall a, YI04.inFP (LLVMFuzzerTestOneInput_c.ltoi_PG longlA) a -> ~ in_roP tfibsegs RLO_A RHI_A a.
Proof. exact (SegRecBase.cif_prog_not_ro _ _ seg_IMG). Qed.
#[local] Hint Resolve YG0q.AR_laws_ok seg_IMG seg_ERRNO seg_ro_below seg_sspx seg_dc_ssp seg_hpg_ro : gpc.
Lemma seg_TL : PALib (PI := PB_seg) B.
Proof. exact (SegRecRest.seg_palib B HB). Qed.
Lemma seg_TLF : PaLibF.PALibF (PI := PB_seg) B.
Proof. exact (SegRecRest.seg_palibf B HB). Qed.
Lemma seg_ML : model_laws (as_universe B).
Proof. exact (SegRecRest.seg_model_laws B HB). Qed.
Lemma seg_PRW : prog_rw tfibsegs B.
Proof. exact (SegRecRest.seg_prw_tfib B HB). Qed.
Lemma seg_SMP : stack_malloc_progressP B.
Proof. exact (SegRecRest.seg_stack_malloc_progress B). Qed.
Lemma seg_ASF : astack_free_law tfibsegs B.
Proof. exact (SegRecRest.seg_astack_free_law B). Qed.
Lemma seg_FFL : frame_flag_lawP tfibsegs B.
Proof. exact (SegRecRest.seg_frame_flag_law B). Qed.
#[local] Hint Resolve seg_TL seg_TLF seg_ML seg_PRW seg_SMP seg_ASF seg_FFL
  SegRecRest.seg_sig_prog_PB SegRecRest.seg_val_objs_PB SegRecRest.seg_val_relro_PB
  YCbp.ameter_triv_laws YCbp.ameter_triv_fs_laws : gpc.

(* ---- the listing facts, by the listing's lib/B/Prog/SegRecLtoi.v (each the walks' own text) ------------------- *)
(* m_file: musl memchr's word-constant window [memchr_loA, memchr_hiA) is read-only (the record's cif_snl_rom), not
   a runtime-owned static and not the errno cell *)
Lemma h_mcrom : m_file_memchr.memchr_rom_fact tfibsegs B.
Proof. exact (SegRecLtoi.seg_mcrom B HB). Qed.
(* LLVMFuzzerTestOneInput: longl is one of the record's program statics and in the image *)
Lemma h_pgs : forall a, YI04.inFP (LLVMFuzzerTestOneInput_c.ltoi_PG longlA) a ->
  Exists (in_zr a) (as_prog_static B) /\ in_img tfibsegs a.
Proof. exact (SegRecLtoi.seg_pgs B HB). Qed.
(* LLVMFuzzerTestOneInput: every pointer word of words[] and of the catalogue rows lies 64 KiB below longl *)
Lemma h_pg_ptr : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Proof. exact SegRecLtoi.seg_pg_ptr. Qed.
(* LLVMFuzzerTestOneInput: snprintf's window ends below the fake stack at every AR state: the listing's image cover
   (SegPa.pa_img_cover at PB_seg) ends at kImgEnd = RtPFCmd.CMD_IMG_HI, and the layout puts the image hull below the
   fake stack (hull_below_F); fuzz_command's lib/B/Rt/RtPFDog.v pa_fake_above_img *)
Lemma h_snp_fake : forall ly S (W : world tfibsegs) mem md, AR tfibsegs B ly S W mem md ->
  RtPFCmd.CMD_IMG_HI <= ly_F ly.
Proof.
intros ly S W mem md (M & LG & _).
pose proof (pa_img_cover (PAImg := PB_seg) ly S md LG) as [_ C2].
pose proof (YG0t.hull_below_F ly (am_layout _ _ _ _ M)) as HF.
unfold RtPFCmd.CMD_IMG_HI. lia.
Qed.
#[local] Hint Resolve h_mcrom h_pgs h_pg_ptr h_snp_fake : gpc.

(* ---- the interceptor rows, at the listing's call targets: the interceptor layer's closings (lib/B/Rt/SegRtClosed.v),
   whose entries RtAPI.PC_<x> / SegRtPC.PC_<x> and stack-protector cells RtAPI.A_SSP_GOT / A_SSP_GUARD are the
   listing's SIG SS_<x> and SegInstB's gotwA / guardA (SegInstB.pc_rtapi / pc_segi), by computation ------------- *)
Lemma r_strlen : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strlen).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strlen) with RtAPI.PC_strlen by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strlen_closed B HB).
Qed.
Lemma r_strcmp : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strcmp).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strcmp) with RtAPI.PC_strcmp by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strcmp_closed B HB).
Qed.
Lemma r_strncmp : forall fx0 : YK11.FPState,
  @RtString.astrncmp_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strncmp).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strncmp) with RtAPI.PC_strncmp by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strncmp_closed B HB).
Qed.
Lemma r_strspn : forall fx0 : YK11.FPState,
  @RtString.astrspn_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strspn) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strspn) with RtAPI.PC_strspn by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strspn_closed B HB).
Qed.
Lemma r_memchr : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc tfibsegs B memchr_loA memchr_hiA (SIG SS___interceptor_trampoline_memchr).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_memchr) with RtAPI.PC_memchr by (vm_compute; reflexivity).
replace memchr_loA with SegRtClosed.memchr_lo by (vm_compute; reflexivity).
replace memchr_hiA with SegRtClosed.memchr_hi by (vm_compute; reflexivity).
exact (SegRtClosed.seg_memchr_closed B HB).
Qed.
Lemma r_strstr : forall fx0 : YK11.FPState,
  @RtSeg.astrstr_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strstr) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strstr) with SegRtPC.PC_strstr by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strstr_closed B HB).
Qed.
Lemma r_isalnum : forall fx0 : YK11.FPState,
  @RtSeg.aisalnum_realizes fx0 rc tfibsegs B (SIG SS_isalnum).
Proof.
intros fx0.
replace (SIG SS_isalnum) with SegRtPC.PC_isalnum by (vm_compute; reflexivity).
exact (SegRtClosed.seg_isalnum_closed B).
Qed.
Lemma r_strncpy : forall fx0 : YK11.FPState,
  @RtSeg.astrncpy_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strncpy).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strncpy) with SegRtPC.PC_strncpy by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strncpy_closed B HB).
Qed.
Lemma r_strrchr : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strrchr).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strrchr) with SegRtPC.PC_strrchr by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strrchr_closed B HB).
Qed.
Lemma r_strtol0 : forall fx0 : YK11.FPState,
  @RtSeg.astrtol0_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strtol) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strtol) with RtAPI.PC_strtol by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strtol0_closed B HB).
Qed.
Lemma r_strchr : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strchr).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strchr) with SegRtPC.PC_strchr by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strchr_closed B HB).
Qed.
Lemma r_strcasecmp : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strcasecmp).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strcasecmp) with SegRtPC.PC_strcasecmp by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strcasecmp_closed B HB).
Qed.
Lemma r_strncasecmp : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_strncasecmp).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_strncasecmp) with SegRtPC.PC_strncasecmp by (vm_compute; reflexivity).
exact (SegRtClosed.seg_strncasecmp_closed B HB).
Qed.
Lemma r_bcmp : forall fx0 : YK11.FPState,
  @abcmp_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_bcmp).
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_bcmp) with 0x43ac4 by (vm_compute; reflexivity).
exact (@SegRtClosed.seg_bcmp_closed fx0 rc B HB).
Qed.
(* snprintf / vsnprintf, row 4, in RtPFSeg's form at RtPFCmd's window (m_refuse, m_file, refuse,
   LLVMFuzzerTestOneInput), and snprintf in RtFormat's form (reac_segconf_parse_file) *)
Lemma r_snprintf_seg : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc tfibsegs B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_snprintf) with RtAPI.PC_snprintf by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_snprintf_closed B HB).
Qed.
Lemma r_vsnprintf_seg : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_avsnprintf_realizes fx0 rc tfibsegs B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_vsnprintf) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_vsnprintf) with SegRtPC.PC_vsnprintf by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_vsnprintf_closed B HB).
Qed.
Lemma r_snprintf_fmt : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc tfibsegs B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_snprintf) with RtAPI.PC_snprintf by (vm_compute; reflexivity).
replace gotwA with RtAPI.A_SSP_GOT by (vm_compute; reflexivity).
replace guardA with RtAPI.A_SSP_GUARD by (vm_compute; reflexivity).
exact (SegRtClosed.seg_rtformat_closed B HB).
Qed.
(* calloc, row 13, at its window cstk: the calloc closing's own window RtLCalloc.SEG_CALLOC_CSTK *)
#[local] Notation cstk := RtLCalloc.SEG_CALLOC_CSTK (only parsing).
Lemma h_cstk : 0 <= cstk /\ LLVMFuzzerTestOneInput_inst.LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.
Lemma r_calloc : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv
    (SIG SS___interceptor_trampoline_calloc) cstk.
Proof.
intros fx0.
replace (SIG SS___interceptor_trampoline_calloc) with SegRtPC.PC_calloc by (vm_compute; reflexivity).
exact (SegRtClosed.seg_acalloc_closed B HB HD fx0).
Qed.

(* ---- the core's rows: checked memset / memcpy, the side-stack frames, the shadow fills (lib/B/Rt/RtClosed.v at
   SegInstB's terms, which are the listing's SIG SS_<x> at PB_seg by conversion, SegInstPB.pb_pc_<x>A) ---------- *)
Lemma r_memset : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc tfibsegs B OSet (SIG SS___asan_memset).
Proof. intros fx0. exact (@RtClosed.seg_asan_memset_closed fx0 rc B HB). Qed.
Lemma r_memcpy : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc tfibsegs B OCpy (SIG SS___asan_memcpy).
Proof. intros fx0. exact (@RtClosed.seg_asan_memcpy_closed fx0 rc B HB). Qed.
Lemma r_sm0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs B 0.
Proof. intros fx0. exact (@RtClosed.seg_stack_malloc0_closed fx0 rc B HB). Qed.
Lemma r_sm1 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs B 1.
Proof. intros fx0. exact (@RtClosed.seg_stack_malloc1_closed fx0 rc B HB). Qed.
Lemma r_sm3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs B 3.
Proof. intros fx0. exact (@RtClosed.seg_stack_malloc3_closed fx0 rc B HB). Qed.
Lemma r_sm5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc tfibsegs B 5.
Proof. intros fx0. exact (@RtClosed.seg_stack_malloc5_closed fx0 rc B HB). Qed.
Lemma r_sf5 : forall fx0 : YK11.FPState,
  @RtStack.astack_free_cls_realizes fx0 rc tfibsegs B (SIG SS___asan_stack_free_5) 5.
Proof. intros fx0. exact (@RtClosed.seg_stack_free5_closed fx0 rc B HB). Qed.
Lemma r_shf5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs B (SIG SS___asan_set_shadow_f5) 0xf5.
Proof. intros fx0. exact (@RtClosed.seg_set_shadow_f5_closed fx0 rc B HB). Qed.
Lemma r_shf8 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs B (SIG SS___asan_set_shadow_f8) 0xf8.
Proof. intros fx0. exact (@RtClosed.seg_set_shadow_f8_closed fx0 rc B HB). Qed.
Lemma r_sh00 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc tfibsegs B (SIG SS___asan_set_shadow_00) 0.
Proof. intros fx0. exact (@RtClosed.seg_set_shadow_00_closed fx0 rc B HB). Qed.
(* the allocator rows under the trivial meter's rules (lib/B/YCbp.v amalloc04_rule_triv / afree04_rule_triv): malloc
   by image B's malloc chain lib/B/YF0w.v tfib_amalloc_realizes, free by image B's free closer lib/B/YF0q.v
   afree_realizes_closed (fuzz_command's CmdProgClosed.v r_malloc4 / r_free4) *)
Lemma r_amalloc4 : forall fx0 : YK11.FPState,
  @amalloc04_rule fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv.
Proof.
intros fx0.
exact (@YCbp.amalloc04_rule_triv fx0 rc YE2k.tfib_sink_head tfibsegs B (pa_segs_low (PAImg := PB_seg))
  (pal_env B seg_TL) (YG0q.AR_laws_ok _ _) seg_ML (@YF0w.tfib_amalloc_realizes fx0 rc B HB HD)).
Qed.
Lemma r_afree4 : forall fx0 : YK11.FPState,
  @afree04_rule fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv.
Proof.
intros fx0.
exact (@YCbp.afree04_rule_triv fx0 rc YE2k.tfib_sink_head tfibsegs B (pa_segs_low (PAImg := PB_seg))
  (pal_env B seg_TL) (YG0q.AR_laws_ok _ _) seg_ML (@YF0q.afree_realizes_closed fx0 rc B HB HD)).
Qed.

#[local] Hint Resolve r_strlen r_strcmp r_strncmp r_strspn r_memchr r_strstr r_isalnum r_strncpy r_strrchr
  r_strtol0 r_strchr r_strcasecmp r_strncasecmp r_bcmp r_snprintf_seg r_vsnprintf_seg r_snprintf_fmt h_cstk
  r_calloc r_memset r_memcpy r_sm0 r_sm1 r_sm3 r_sm5 r_sf5 r_shf5 r_shf8 r_sh00 r_amalloc4 r_afree4 : gpc.

(* m_refuse's and m_file's snprintf row names RtPFCmd's .got word and guard: the same numbers as SegInstB's *)
Lemma r_snprintf_cmd : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc tfibsegs B RtPFCmd.CMD_IMG_LO RtPFCmd.CMD_IMG_HI RtPFCmd.CMD_SNP_CR
    (SIG SS___interceptor_trampoline_snprintf) RtPFCmd.CMD_GOTW RtAPI.A_SSP_GUARD.
Proof. exact r_snprintf_seg. Qed.
#[local] Hint Resolve r_snprintf_cmd : gpc.

(* ---- G4 + G5: lib/B/Prog/SegG45.v's composition at PB_seg -------------------------------------------------- *)
Lemma cl_reac_segconf_find : forall fx0 : YK11.FPState,
  reac_segconf_find_c.reac_segconf_find_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_find)
    STK_reac_segconf_find RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_find (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_init : forall fx0 : YK11.FPState,
  reac_segconf_init_c.reac_segconf_init_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_init)
    STK_reac_segconf_init.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_init (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_role_file : forall fx0 : YK11.FPState,
  reac_segconf_role_file_c.reac_segconf_role_file_contract (fx := fx0) tfibsegs B
    (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_role_file (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_role : forall fx0 : YK11.FPState,
  reac_segconf_role_c.reac_segconf_role_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_role)
    STK_reac_segconf_role RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_role (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_ignore_file : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_c.reac_segconf_ignore_file_contract (fx := fx0) tfibsegs B
    (BASE + AF_reac_segconf_ignore_file) STK_reac_segconf_ignore_file RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_ignore_file (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_ignored : forall fx0 : YK11.FPState,
  reac_segconf_ignored_c.reac_segconf_ignored_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_ignored)
    STK_reac_segconf_ignored RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_ignored (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_model : forall fx0 : YK11.FPState,
  reac_segconf_model_c.reac_segconf_model_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_model)
    STK_reac_segconf_model RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_model (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_absent : forall fx0 : YK11.FPState,
  check_absent_c.check_absent_contract (fx := fx0) tfibsegs B (BASE + AF_check_absent) STK_check_absent RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_absent (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_segments : forall fx0 : YK11.FPState,
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog.check_segments_c.check_segments_contract (fx := fx0)
    tfibsegs B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_segments (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_role : forall fx0 : YK11.FPState,
  check_role_c.check_role_contract (fx := fx0) tfibsegs B (BASE + AF_check_role) STK_check_role.
Proof. intros fx0. eapply (SegG45.cl_check_role (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_model : forall fx0 : YK11.FPState,
  check_model_c.check_model_contract (fx := fx0) tfibsegs B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_model (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_ignore : forall fx0 : YK11.FPState,
  check_ignore_c.check_ignore_contract (fx := fx0) tfibsegs B (BASE + AF_check_ignore) STK_check_ignore.
Proof. intros fx0. eapply (SegG45.cl_check_ignore (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_provenance : forall fx0 : YK11.FPState,
  check_provenance_c.check_provenance_contract (fx := fx0) tfibsegs B (BASE + AF_check_provenance)
    STK_check_provenance RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_provenance (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_refusals : forall fx0 : YK11.FPState,
  check_refusals_c.check_refusals_contract (fx := fx0) tfibsegs B (BASE + AF_check_refusals) STK_check_refusals.
Proof. intros fx0. eapply (SegG45.cl_check_refusals (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_address : forall fx0 : YK11.FPState,
  check_address_c.check_address_contract (fx := fx0) tfibsegs B (BASE + AF_check_address) STK_check_address
    RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_address (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_knock_refused : forall fx0 : YK11.FPState,
  check_knock_refused_c.check_knock_refused_contract (fx := fx0) tfibsegs B (BASE + AF_check_knock_refused)
    STK_check_knock_refused RLO_A RHI_A seg_litA_fz gotwA guardA.
Proof. intros fx0. eapply (SegG45.cl_check_knock_refused (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_check_declared : forall fx0 : YK11.FPState,
  check_declared_c.check_declared_contract (fx := fx0) tfibsegs B (BASE + AF_check_declared) STK_check_declared
    RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_check_declared (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_name_ok : forall fx0 : YK11.FPState,
  name_ok_c.name_ok_contract (fx := fx0) tfibsegs B (BASE + AF_name_ok) STK_name_ok RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_name_ok (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_declared_vlan_split : forall fx0 : YK11.FPState,
  reac_declared_vlan_split_c.reac_declared_vlan_split_contract (fx := fx0) tfibsegs B
    (BASE + AF_reac_declared_vlan_split) STK_reac_declared_vlan_split RLO_A RHI_A gotwA guardA.
Proof. intros fx0. eapply (SegG45.cl_reac_declared_vlan_split (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_declared_vlan_add : forall fx0 : YK11.FPState,
  reac_declared_vlan_add_c.reac_declared_vlan_add_contract (fx := fx0) tfibsegs B (BASE + AF_reac_declared_vlan_add)
    STK_reac_declared_vlan_add RLO_A RHI_A.
Proof. intros fx0. eapply (SegG45.cl_reac_declared_vlan_add (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_declared : forall fx0 : YK11.FPState,
  reac_segconf_declared_c.reac_segconf_declared_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_declared)
    STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Proof. intros fx0. eapply (SegG45.cl_reac_segconf_declared (PI := PB_seg)); eauto with gpc. Qed.

(* ---- G2: lib/B/Prog/SegG2.v's composition at PB_seg ------------------------------------------------------- *)
Lemma cl_fuzz_catalogue_row : forall fx0 : YK11.FPState,
  fuzz_catalogue_row_c.fuzz_catalogue_row_contract (fx := fx0) tfibsegs B (BASE + AF_fuzz_catalogue_row)
    STK_fuzz_catalogue_row RLO_A RHI_A catA.
Proof. intros fx0. eapply (SegG2.cl_fuzz_catalogue_row (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_box_catalogue : forall fx0 : YK11.FPState,
  reac_box_catalogue_c.reac_box_catalogue_contract (fx := fx0) tfibsegs B (BASE + AF_reac_box_catalogue)
    STK_reac_box_catalogue catA.
Proof. intros fx0. eapply (SegG2.cl_reac_box_catalogue (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_box_catalogue_by_token : forall fx0 : YK11.FPState,
  reac_box_catalogue_by_token_c.reac_box_catalogue_by_token_contract (fx := fx0) tfibsegs B
    (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Proof. intros fx0. eapply (SegG2.cl_reac_box_catalogue_by_token (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_ieq : forall fx0 : YK11.FPState,
  ieq_c.ieq_contract (fx := fx0) tfibsegs B (BASE + AF_ieq) STK_ieq RLO_A RHI_A.
Proof. intros fx0. eapply (SegG2.cl_ieq (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_m_find : forall fx0 : YK11.FPState,
  m_find_c.m_find_contract (fx := fx0) tfibsegs B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Proof. intros fx0. eapply (SegG2.cl_m_find (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_strip : forall fx0 : YK11.FPState,
  strip_c.strip_contract (fx := fx0) tfibsegs B (BASE + AF_strip) STK_strip.
Proof. intros fx0. eapply (SegG2.cl_strip (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_fold : forall fx0 : YK11.FPState,
  fold_c.fold_contract (fx := fx0) tfibsegs B (BASE + AF_fold) STK_fold.
Proof. intros fx0. eapply (SegG2.cl_fold (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_m_refuse : forall fx0 : YK11.FPState,
  m_refuse_c.m_refuse_contract (fx := fx0) tfibsegs B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz
    gotwA guardA.
Proof. intros fx0. eapply (SegG2.cl_m_refuse (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_m_file : forall fx0 : YK11.FPState,
  m_file_c.m_file_contract (fx := fx0) tfibsegs B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz wordsA
    rolesA catA gotwA guardA.
Proof. intros fx0. eapply (SegG2.cl_m_file (PI := PB_seg)); eauto with gpc. Qed.
#[local] Hint Resolve cl_fuzz_catalogue_row cl_reac_box_catalogue cl_reac_box_catalogue_by_token cl_ieq cl_m_find
  cl_strip cl_fold cl_m_refuse cl_m_file : gpc.

(* ---- G3: trim, refuse, cross_check, reac_segconf_parse_file, reac_segconf_parse ----------------------------- *)
(* refuse's snprintf window: RtPFCmd's two ranges lie in [0x10000, kImgEnd) *)
Lemma seg_snp_cr_img : Forall (fun r : Z * Z => 65536 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd)
  RtPFCmd.CMD_SNP_CR.
Proof.
unfold RtPFCmd.CMD_SNP_CR. repeat constructor; cbn; apply Z.leb_le; vm_compute; reflexivity.
Qed.
Lemma cl_trim : forall fx0 : YK11.FPState,
  trim_c.trim_contract (fx := fx0) tfibsegs B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Proof. intros fx0. eapply (trim.trim_walk (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_refuse : forall fx0 : YK11.FPState,
  refuse_c.refuse_contract (fx := fx0) tfibsegs B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof.
intros fx0. eapply (refuse.refuse_walk (PI := PB_seg) B) with (cr := RtPFCmd.CMD_SNP_CR); eauto using seg_snp_cr_img with gpc.
Qed.
#[local] Hint Resolve cl_trim cl_refuse : gpc.
Lemma cl_cross_check : forall fx0 : YK11.FPState,
  cross_check_c.cross_check_contract (fx := fx0) tfibsegs B (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A
    seg_litA_rc gotwA guardA.
Proof. intros fx0. eapply (cross_check.cross_check_walk_B (PI := PB_seg)); eauto with gpc. Qed.
Lemma cl_reac_segconf_parse_file : forall fx0 : YK11.FPState,
  reac_segconf_parse_file_c.reac_segconf_parse_file_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_parse_file)
    STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof. intros fx0. eapply (reac_segconf_parse_file.reac_segconf_parse_file_walk (PI := PB_seg)); eauto with gpc. Qed.
#[local] Hint Resolve cl_cross_check cl_reac_segconf_parse_file : gpc.
Lemma cl_reac_segconf_parse : forall fx0 : YK11.FPState,
  reac_segconf_parse_c.reac_segconf_parse_contract (fx := fx0) tfibsegs B (BASE + AF_reac_segconf_parse)
    STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Proof. intros fx0. eapply (reac_segconf_parse.reac_segconf_parse_walk (PI := PB_seg)); eauto with gpc. Qed.

(* ---- G1: LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput.v pb_LLVMFuzzerTestOneInput) --------------- *)
#[local] Hint Resolve cl_reac_segconf_find cl_reac_segconf_init cl_reac_segconf_role_file cl_reac_segconf_role
  cl_reac_segconf_ignore_file cl_reac_segconf_ignored cl_reac_segconf_model cl_check_absent cl_check_segments
  cl_check_role cl_check_model cl_check_ignore cl_check_provenance cl_check_refusals cl_check_address
  cl_check_knock_refused cl_check_declared cl_name_ok cl_reac_declared_vlan_split cl_reac_declared_vlan_add
  cl_reac_segconf_declared cl_reac_segconf_parse : gpc.
(* snprintf's window (snp_lo, snp_hi, snp_cr) := RtPFCmd's (CMD_IMG_LO, CMD_IMG_HI, CMD_SNP_CR), the numbers of
   r_snprintf_seg; the window's facts by computation *)
Lemma seg_hsnp_lit : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  RtPFCmd.CMD_IMG_LO <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Proof.
assert (H : forallb (fun x => (RtPFCmd.CMD_IMG_LO <=? seg_litA_fz x) &&
  (seg_litA_fz x + Z.of_nat (length x) + 1 <=? gotwA)) LLVMFuzzerTestOneInput_c.LTOI_LITS = true)
  by (vm_compute; reflexivity).
intros x Hx. rewrite forallb_forall in H. specialize (H x Hx). apply andb_prop in H as [H1 H2].
split; apply Z.leb_le; assumption.
Qed.
Lemma seg_hsnp_cr : Forall (fun r : Z * Z => RtPFCmd.CMD_IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= RtPFCmd.CMD_IMG_HI)
  RtPFCmd.CMD_SNP_CR.
Proof. exact seg_snp_cr_img. Qed.
Lemma seg_hsnp_lo : 0 <= RtPFCmd.CMD_IMG_LO.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma seg_hsnp_ceil : RtPFCmd.CMD_IMG_HI <= alloc_ceiling.
Proof.
pose proof (@YM05.alloc_ceiling_value rc) as [[Hlo _] _].
assert (H : RtPFCmd.CMD_IMG_HI <= 140735332483072) by (apply Z.leb_le; vm_compute; reflexivity).
lia.
Qed.
#[local] Hint Resolve HB seg_hsnp_lit seg_hsnp_cr seg_hsnp_lo seg_hsnp_ceil : gpc.
Lemma cl_LLVMFuzzerTestOneInput : forall fx0 : YK11.FPState,
  @LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv
    (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA
    rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof.
intros fx0.
eapply (@LLVMFuzzerTestOneInput.pb_LLVMFuzzerTestOneInput fx0 rc YE2k.tfib_sink_head PB_seg B YCbp.ameter_triv)
  with (cstk := cstk) (snp_lo := RtPFCmd.CMD_IMG_LO) (snp_hi := RtPFCmd.CMD_IMG_HI) (snp_cr := RtPFCmd.CMD_SNP_CR);
  eauto with gpc.
Qed.

(* ---- the entry, at SegInstB's A_LLVMFuzzerTestOneInput_A (SegTopB.v's HLTOI) ------------------------------- *)
Theorem seg_ltoi_all : forall fx0 : YK11.FPState,
  @LLVMFuzzerTestOneInput_c.LLVMFuzzerTestOneInput_contract fx0 rc YE2k.tfib_sink_head tfibsegs B YCbp.ameter_triv
    A_LLVMFuzzerTestOneInput_A STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA rolesA gotwA
    guardA seg_litA_fz seg_litA_rc.
Proof. intros fx0. rewrite <- SegInstPB.pb_entry_LLVMFuzzerTestOneInput. exact (cl_LLVMFuzzerTestOneInput fx0). Qed.
End closed.

(* the open parts are seg_ltoi_all's arguments after B (its Section hypotheses), not axioms *)
About seg_ltoi_all.
Print Assumptions seg_ltoi_all.
