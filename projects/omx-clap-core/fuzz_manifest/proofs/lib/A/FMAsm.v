(* The final instance of fuzz_manifest's program part at fm's symbols TfibB: every callee contract and image fact that
   the harness assembly fm_lib_x (FMW_harness.v) takes, from the walk theorems (the FMW files), the runtime contracts
   (the FM files of the runtime functions),
   the relocated core and the instance facts (FMInst.v, FMInstB.v). Every walk theorem is generic in the sink instance
   {SK}; it is passed explicitly here as the image's instance AE2k.tfib_sink_head (the one FMW_harness.v elaborates its
   hypotheses with). This file loads no plain-side instance (FMPlain.v / FMTop.v are not in its closure).
   The bcmp wrapper's contract at PC_bcmp = 0x412e8 (expected_spec_holds' premise) is FMbcmp.fm_bcmp_TfibB, the
   relocated cgif_file lib/A/AE2s.v bcmp_icpt_contract. fm_lib_x_TfibB has no premise. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK04 YA0i YA0n YG00 YG05 YG0f YG0n YG0d YG0q YCbp YC5d YI16 YM05 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AF0l AD2l ACeg ACej AD1u AE2q AE2r.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
FMH_Base FMH_Rt FMH_Fn FMH_Harness FMW_seg FMW_g3kit FMW_llvmf0 FMW_cno0 FMpoisonR FMInst FMInstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require
  AE2k AF0w AF0q FMpoisonS FMpoisonW FMstrlen_rt FMstrchr FMstrncmp FMmemchr FMsnprintf FMstrstr FMstrncasecmp FMctype
  FMbcmp
  FMW_fuzz_alloc_live FMW_fuzz_alloc_peak FMW_fuzz_alloc_peak_reset FMW_fuzz_alloc_fail FMW_fuzz_malloc FMW_fuzz_free
  FMW_names FMW_readings FMW_has_prefixed FMW_plain FMW_ex_all FMW_as_ruled FMW_cno FMW_check_bounded_alloc
  FMW_check_as_written FMW_check_reject_clean FMW_check_reject_clean_starved FMW_harness.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the image's sink instance is the only one in this file's context: statement types that take {SK} (the allocator
   rules, the walk specs) resolve to it; the walk theorems get it explicitly with @ below. No plain-side instance is
   loaded here (the next line checks that the instance found is AE2k's). *)
#[local] Existing Instance AE2k.tfib_sink_head.
Example asm_sink_head_is_image : @YI16.sk_ofl_head _ = @YI16.sk_ofl_head AE2k.tfib_sink_head.
Proof. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the core, the runtime and the image facts ---- *)
Lemma asm_laws : AR_laws tfibsegs TfibB.
Proof. exact (AR_laws_ok tfibsegs TfibB). Qed.

Lemma asm_ail : @asink_img_laws AE2k.tfib_sink_head tfibsegs TfibB AE2k.tfib_K.
Proof. eapply tfib_AIL; first [exact TfibB_syms | apply AR_laws_ok]. Qed.

Lemma asm_ml : model_laws (as_universe TfibB).
Proof. exact (model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms)). Qed.

Lemma asm_amalloc : amalloc04_rule tfibsegs TfibB ameter_triv.
Proof.
  exact (amalloc04_rule_triv tfibsegs TfibB tfib_segs_low (tl_env TfibB fm_tfib_lib) asm_laws asm_ml
    (AF0w.tfib_amalloc_realizes TfibB TfibB_syms (fun t => eq_refl))).
Qed.

Lemma asm_afree : afree04_rule tfibsegs TfibB ameter_triv.
Proof.
  exact (afree04_rule_triv tfibsegs TfibB tfib_segs_low (tl_env TfibB fm_tfib_lib) asm_laws asm_ml
    (AF0q.afree_realizes_closed TfibB TfibB_syms (fun t => eq_refl))).
Qed.

(* __asan_memcpy (0x51a68) and __asan_memset (0x51f04), cgif_file's A/ACed.v tfibX_AMEMCPY / tfibX_AMEMSET *)
Lemma asm_amemcpy : aintrin_realizes tfibsegs TfibB OCpy FM_asan_memcpy.
Proof.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull Hsrc.
  exact (asan_memcpy_realizes TfibB asm_laws TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra
    Hhull Hsrc).
Qed.

Lemma asm_amemcpy_cno : aintrin_realizes tfibsegs TfibB OCpy PC_memcpy.
Proof. exact asm_amemcpy. Qed.

Lemma asm_amemset : aintrin_realizes tfibsegs TfibB OSet PC_memset.
Proof.
  intros ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (asan_memset_realizes TfibB asm_laws TfibB_syms ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull
    Ham).
Qed.

Lemma asm_poison : FMpoisonS.apoison16_realizes tfibsegs TfibB PC_poison.
Proof. exact (FMpoisonW.tfib_poison16 TfibB asm_laws TfibB_syms). Qed.

Lemma asm_unpoison : FMpoisonS.aunpoison16_realizes tfibsegs TfibB PC_unpoison.
Proof. exact (FMpoisonW.tfib_unpoison16 TfibB asm_laws TfibB_syms). Qed.

Lemma asm_strlen : astrlen_realizes tfibsegs TfibB PC_strlen.
Proof. exact (FMstrlen_rt.astrlen_holds TfibB asm_laws TfibB_syms). Qed.
Lemma asm_strchr : astrchr_realizes tfibsegs TfibB PC_strchr.
Proof. exact (FMstrchr.astrchr_holds TfibB asm_laws TfibB_syms). Qed.
Lemma asm_strncmp : astrncmp_realizes tfibsegs TfibB PC_strncmp.
Proof. exact (FMstrncmp.astrncmp_holds TfibB asm_laws TfibB_syms). Qed.
Lemma asm_memchr : amemchr_realizes tfibsegs TfibB PC_memchr.
Proof. exact (FMmemchr.amemchr_holds TfibB asm_laws TfibB_syms). Qed.
Lemma asm_snprintf : asnprintf_realizes tfibsegs TfibB PC_snprintf.
Proof. exact (FMsnprintf.fm_snprintf_realizes TfibB asm_laws TfibB_syms). Qed.
Lemma asm_strstr : astrstr_realizes tfibsegs TfibB PC_strstr.
Proof. exact (FMstrstr.fm_astrstr TfibB asm_laws TfibB_syms). Qed.
Lemma asm_strncasecmp : astrncasecmp_realizes tfibsegs TfibB PC_strncasecmp.
Proof. exact (FMstrncasecmp.fm_astrncasecmp_realizes TfibB TfibB_syms). Qed.
Lemma asm_isalnum : aisalnum_realizes tfibsegs TfibB PC_isalnum.
Proof. exact (FMctype.aisalnum_holds TfibB asm_laws). Qed.

Lemma asm_img : fm_img_facts tfibsegs TfibB.
Proof. exact (fm_img_facts_holds TfibB TfibB_syms). Qed.
Lemma asm_fb : FmB TfibB.
Proof. exact (fm_FmB TfibB TfibB_syms). Qed.
Lemma asm_g3 : g3_cells TfibB.
Proof. split; reflexivity. Qed.

(* ---- the program's functions, below LLVMFuzzerTestOneInput ---- *)
Lemma asm_alive : fuzz_alloc_live_spec tfibsegs TfibB.
Proof. exact (@FMW_fuzz_alloc_live.fuzz_alloc_live_holds fx rc AE2k.tfib_sink_head TfibB). Qed.
Lemma asm_apeak : fuzz_alloc_peak_spec tfibsegs TfibB.
Proof. exact (@FMW_fuzz_alloc_peak.fuzz_alloc_peak_holds fx rc AE2k.tfib_sink_head TfibB). Qed.
Lemma asm_apreset : fuzz_alloc_peak_reset_spec tfibsegs TfibB.
Proof. exact (@FMW_fuzz_alloc_peak_reset.fuzz_alloc_peak_reset_holds fx rc AE2k.tfib_sink_head TfibB TfibB_syms). Qed.
Lemma asm_afail : fuzz_alloc_fail_spec tfibsegs TfibB.
Proof. exact (@FMW_fuzz_alloc_fail.fuzz_alloc_fail_holds fx rc AE2k.tfib_sink_head TfibB TfibB_syms). Qed.

Lemma asm_malloc : fuzz_malloc_spec tfibsegs TfibB CTX_fuzz_malloc.
Proof.
  exact (@FMW_fuzz_malloc.fuzz_malloc_holds fx rc AE2k.tfib_sink_head TfibB TfibB_syms fm_tfib_lib asm_amalloc asm_poison
    CTX_fuzz_malloc).
Qed.
Lemma asm_free : fuzz_free_spec tfibsegs TfibB CTX_fuzz_free.
Proof.
  exact (@FMW_fuzz_free.fuzz_free_holds fx rc AE2k.tfib_sink_head TfibB TfibB_syms fm_tfib_lib fm_univ_holds asm_unpoison
    asm_afree).
Qed.

Lemma asm_has_prefixed : has_prefixed_spec tfibsegs TfibB.
Proof.
  exact (@FMW_has_prefixed.has_prefixed_holds fx rc AE2k.tfib_sink_head TfibB fm_tfib_lib asm_img asm_isalnum asm_strlen
    asm_strncmp asm_strstr).
Qed.

Lemma asm_readings : forall CTX, readings_spec tfibsegs TfibB CTX.
Proof.
  intros CTX.
  exact (@FMW_readings.readings_holds fx rc AE2k.tfib_sink_head TfibB CTX asm_g3 asm_img asm_strlen asm_snprintf
    asm_strstr asm_strncmp asm_strncasecmp asm_strchr asm_isalnum asm_malloc asm_free asm_has_prefixed).
Qed.

Lemma asm_names : names_spec tfibsegs TfibB CTX_lv2_locate_manifest_names.
Proof.
  apply (@FMW_names.names_holds fx rc AE2k.tfib_sink_head TfibB CTX_lv2_locate_manifest_names
    (map (fun c => FMW_names.NM_RA :: tl c) CTX_lv2_locate_manifest_names)).
  - intros c Hc. exact (in_map (fun c => FMW_names.NM_RA :: tl c) _ c Hc).
  - apply asm_readings.
Qed.

Lemma asm_plain : plain_spec tfibsegs TfibB.
Proof. exact (@FMW_plain.plain_spec_holds fx rc AE2k.tfib_sink_head TfibB fm_tfib_lib asm_img asm_strlen). Qed.

Lemma asm_expected : expected_spec tfibsegs TfibB.
Proof.
  exact (@FMW_ex_all.expected_spec_holds fx rc AE2k.tfib_sink_head TfibB fm_tfib_lib asm_img asm_strlen asm_strchr
    asm_strncmp FMbcmp.fm_bcmp_TfibB asm_plain).
Qed.

Lemma asm_as_ruled : as_ruled_spec tfibsegs TfibB CTX_as_ruled.
Proof.
  apply (@FMW_as_ruled.as_ruled_holds fx rc AE2k.tfib_sink_head TfibB CTX_lv2_locate_manifest_names asm_names).
  - cbv [CTX_lv2_locate_manifest_names]. repeat (first [left; reflexivity | right]).
  - exact asm_expected.
  - exact asm_img.
Qed.

Lemma asm_cno : check_no_overread_spec tfibsegs TfibB CTX_check_no_overread.
Proof.
  exact (@FMW_cno.check_no_overread_holds fx rc AE2k.tfib_sink_head TfibB asm_fb fm_univ_holds asm_amalloc asm_afree
    asm_amemcpy_cno asm_amemset asm_names).
Qed.

Lemma asm_cba : check_bounded_alloc_spec tfibsegs TfibB.
Proof. exact (@FMW_check_bounded_alloc.check_bounded_alloc_holds fx rc AE2k.tfib_sink_head TfibB). Qed.

Lemma asm_caw : check_as_written_spec tfibsegs TfibB.
Proof. exact (@FMW_check_as_written.check_as_written_holds fx rc AE2k.tfib_sink_head TfibB asm_expected). Qed.

Lemma asm_crc : check_reject_clean_spec tfibsegs TfibB.
Proof. exact (@FMW_check_reject_clean.check_reject_clean_holds fx rc AE2k.tfib_sink_head TfibB asm_alive). Qed.

Lemma asm_starved : check_reject_clean_starved_spec tfibsegs TfibB CTX_check_reject_clean_starved.
Proof.
  apply (@FMW_check_reject_clean_starved.check_reject_clean_starved_holds fx rc AE2k.tfib_sink_head TfibB
    CTX_lv2_locate_manifest_names asm_alive asm_afail asm_names).
  - cbv [CTX_lv2_locate_manifest_names]. repeat (first [left; reflexivity | right]).
  - exact asm_crc.
  - exact asm_img.
Qed.

(* the harness assembly at fm's symbols *)
Theorem fm_lib_x_TfibB : fm_lib_contract_x (LS := checksum_shape) TfibB ameter_triv (fun _ => 0) (fun _ => 0).
Proof.
  exact (@FMW_harness.fm_lib_x fx rc TfibB asm_ail asm_fb asm_img fm_univ_holds asm_amalloc asm_afree asm_amemcpy
    asm_strlen asm_memchr asm_snprintf asm_alive asm_apreset asm_apeak asm_names asm_plain asm_as_ruled asm_cno asm_cba
    asm_caw asm_crc asm_starved).
Qed.
End a.
