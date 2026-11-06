(* fm.asan-ubsan (pin ca61e5c9eabc0050): lib/B/FMTfibTop.v fm_llvmf_walk, the walk of LLVMFuzzerTestOneInput (B 0x8097c)
   at fm's symbols TfibB, as fm_llvmf_walk_holds, by lib/B/FMW_llvmfZ.v llvmf_walk applied at TfibB; and fm's two image-B
   statements Statements.asan_ubsan_agrees / asan_ubsan_halts from it by lib/B/FMFinal.v's _of_walk theorems
   (fm_asan_ubsan_agrees_B, fm_asan_ubsan_halts_B).
   llvmf_walk's 17 Section hypotheses, each proved here from B lemmas (no hypothesis is left):
     FB       lib/B/FMInstB.v fm_FmB_TfibB
     IMG      lib/B/FMInst.v fm_img_facts_TfibB
     UNIV     lib/B/FMInst.v fm_univ_holds
     AMALLOC  Reusable/YCbp.v amalloc04_rule_triv over ReusableB/YF0w.v tfib_amalloc_realizes (fmapp_amalloc)
     AFREE    Reusable/YCbp.v afree04_rule_triv over ReusableB/YF0q.v afree_realizes_closed (fmapp_afree)
     MEMCHR   lib/B/FMmemchr.v amemchr_holds (fmapp_memchr)
     AICPY    ReusableB/YE2q.v asan_memcpy_realizes, the contract at __asan_memcpy 0x51ac8 = FM_asan_memcpy (fmapp_aicpy)
     CNO      lib/B/FMW_cno.v check_no_overread_holds; its memcpy / memset premises at __asan_memcpy 0x51ac8 /
              __asan_memset 0x51f64 (lib/B/FMW_cno0.v PC_memcpy / PC_memset) from ReusableB/YE2q.v / YE2r.v (fmapp_cno)
     ALIVE    lib/B/FMW_fuzz_alloc_live.v fuzz_alloc_live_holds
     APRESET  lib/B/FMW_fuzz_alloc_peak_reset.v fuzz_alloc_peak_reset_holds
     APEAK    lib/B/FMW_fuzz_alloc_peak.v fuzz_alloc_peak_holds
     NAMES    lib/B/FMW_names.v names_holds over lib/B/FMW_readings.v readings_holds, whose callee contracts are the
              B runtime lemmas (FMstrlen_rt, FMsnprintf, FMstrstr, FMstrncmp, FMstrncasecmp, FMstrchr, FMctype),
              fuzz_malloc_holds / fuzz_free_holds over FMpoisonW's tfib_poison16 / tfib_unpoison16, and has_prefixed
              (lib/B/FMW_has_prefixed.v has_prefixed_holds over lib/B/FMW_name_char.v name_char_holds) (fmapp_names)
     CBA      lib/B/FMW_check_bounded_alloc.v check_bounded_alloc_holds
     CAW      lib/B/FMW_check_as_written.v check_as_written_holds over lib/B/FMW_ex_all.v expected_spec_holds, whose
              bcmp premise is lib/B/FMbcmp.v fm_bcmp_TfibB and whose plain premise is lib/B/FMW_plain.v plain_spec_holds
     CRC      lib/B/FMW_check_reject_clean.v check_reject_clean_holds
     STARVED  lib/B/FMW_check_reject_clean_starved.v check_reject_clean_starved_holds (names called from 0x80fd4;
              fuzz_alloc_fail from lib/B/FMW_fuzz_alloc_fail.v)
     CRT      lib/B/FMW_crt.v check_round_trip_holds, with lib/B/FMW_as_ruled.v as_ruled_holds (names called from
              0x81ae8) and plain_spec_holds *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YF0m YD2l YCej YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn FMW_seg FMW_llvmf0 FMW_llvmfZ.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YG05.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YCeg.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YF0w.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YF0q.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YE2q.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMInst.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMInstB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMmemchr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_live.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_peak.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_peak_reset.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrlen_rt.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMsnprintf.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrstr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrncmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrncasecmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrchr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMctype.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMpoisonW.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_malloc.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_free.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_g3kit.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_rd_base.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_readings.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_names.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMFinal.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YE2r.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMbcmp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_fail.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_name_char.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_has_prefixed.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_plain.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_ex_all.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_cno0.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_cno.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_bounded_alloc.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_as_written.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_reject_clean.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_reject_clean_starved.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_as_ruled.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_crt.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
Import ListNotations.
Open Scope Z_scope.

Module RG05 := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YG05.
Module RCeg := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YCeg.
Module RF0w := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YF0w.
Module RF0q := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YF0q.
Module RE2q := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YE2q.
Module FIN := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMInst.
Module FIB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMInstB.
Module FMC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMmemchr.
Module FAL := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_live.
Module FAP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_peak.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_peak_reset.
Module FSL := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrlen_rt.
Module FSN := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMsnprintf.
Module FSS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrstr.
Module FSC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrncmp.
Module FSI := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrncasecmp.
Module FCH := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMstrchr.
Module FCT := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMctype.
Module FPW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMpoisonW.
Module FFM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_malloc.
Module FFF := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_free.
Module FG3 := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_g3kit.
Module FRB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_rd_base.
Module FRD := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_readings.
Module FNM := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_names.
Module RE2r := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB.YE2r.
Module FBC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMbcmp.
Module FFL := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_fuzz_alloc_fail.
Module FNC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_name_char.
Module FHP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_has_prefixed.
Module FPL := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_plain.
Module FEA := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_ex_all.
Module FC0 := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_cno0.
Module FCN := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_cno.
Module FCB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_bounded_alloc.
Module FCW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_as_written.
Module FCR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_reject_clean.
Module FSV := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_check_reject_clean_starved.
Module FAS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_as_ruled.
Module FRT := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMW_crt.

(* AMALLOC: the trivial-meter malloc rule from the allocator contract, as lib/A/FMTfibParts.v builds it for A's TfibB
   (TfibB's dhash is tfib_dhash by definition) *)
Lemma fmapp_amalloc : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @amalloc04_rule fx rc tfib_sink_head tfibsegs TfibB ameter_triv.
Proof.
  intros fx rc.
  exact (amalloc04_rule_triv tfibsegs TfibB RCeg.tfib_segs_low (RCeg.tl_env TfibB FIN.fm_tfib_lib)
    (AR_laws_ok tfibsegs TfibB) (RG05.model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms))
    (RF0w.tfib_amalloc_realizes TfibB TfibB_syms (fun t => eq_refl))).
Qed.

(* AFREE: the same for free *)
Lemma fmapp_afree : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @afree04_rule fx rc tfib_sink_head tfibsegs TfibB ameter_triv.
Proof.
  intros fx rc.
  exact (afree04_rule_triv tfibsegs TfibB RCeg.tfib_segs_low (RCeg.tl_env TfibB FIN.fm_tfib_lib)
    (AR_laws_ok tfibsegs TfibB) (RG05.model_laws_ok (as_universe TfibB) (ts_universe TfibB TfibB_syms))
    (RF0q.afree_realizes_closed TfibB TfibB_syms (fun t => eq_refl))).
Qed.

(* MEMCHR: memchr's runtime contract at PC_memchr *)
Lemma fmapp_memchr : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @amemchr_realizes fx rc tfibsegs TfibB PC_memchr.
Proof. intros fx rc. exact (FMC.amemchr_holds TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.

(* AICPY: the copy contract at __asan_memcpy, the callee of the walk's two memcpy calls (0x80a94, 0x80ae0) *)
Lemma fmapp_aicpy : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @aintrin_realizes fx rc tfibsegs TfibB OCpy FM_asan_memcpy.
Proof. intros fx rc. exact (RE2q.asan_memcpy_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.

(* CNO's copy and fill contracts: __asan_memcpy 0x51ac8 and __asan_memset 0x51f64 (lib/B/FMW_cno0.v) *)
Lemma fmapp_amemcpy : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @aintrin_realizes fx rc tfibsegs TfibB OCpy FC0.PC_memcpy.
Proof. intros fx rc. exact (RE2q.asan_memcpy_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms). Qed.

Lemma fmapp_amemset : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @aintrin_realizes fx rc tfibsegs TfibB OSet FC0.PC_memset.
Proof.
  intros fx rc ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn Hdst Ham Hra Hhull _.
  exact (RE2r.asan_memset_realizes TfibB (AR_laws_ok tfibsegs TfibB) TfibB_syms ly S W regs mem md d x n HPRE
    G10 G11 G12 Hn Hd Hdn Hdst Hra Hhull Ham).
Qed.

(* names' callers (each a one-entry chain) seen from readings: names' own return address NM_RA, the one entry of
   CTX_lv2_locate_manifest_readings *)
Lemma fmapp_names_ctx : forall c, In c CTX_lv2_locate_manifest_names ->
  In (FNM.NM_RA :: tl c) CTX_lv2_locate_manifest_readings.
Proof.
  intros c Hc. unfold CTX_lv2_locate_manifest_names in Hc.
  repeat (destruct Hc as [<- | Hc]; [left; reflexivity |]). destruct Hc.
Qed.

(* readings is called from names only *)
Lemma fmapp_rd_ctx : incl CTX_lv2_locate_manifest_readings [[FRB.RD_NAMES_RA]].
Proof. intros c Hc. exact Hc. Qed.

(* the shadow-base cells readings' walk reads: TfibB's .got slot 0x99c98 and its cell 0xa2078 *)
Lemma fmapp_cells : FG3.g3_cells TfibB.
Proof. split; reflexivity. Qed.

(* names' callers at 0x80fd4 (check_reject_clean_starved) and 0x81ae8 (as_ruled) *)
Lemma fmapp_ctx_starved : In [0x80fd4] CTX_lv2_locate_manifest_names.
Proof. cbv [CTX_lv2_locate_manifest_names]. repeat (first [left; reflexivity | right]). Qed.

Lemma fmapp_ctx_as_ruled : In [0x81ae8] CTX_lv2_locate_manifest_names.
Proof. cbv [CTX_lv2_locate_manifest_names]. repeat (first [left; reflexivity | right]). Qed.

(* the closed B facts the lane theorems' Section hypotheses ask for: AR's laws, fm's symbols and library facts, the
   runtime contracts, the G1 counters, the shadow-base cells, and a call site of names *)
Local Ltac fmapp_leaf := first
  [ exact (AR_laws_ok tfibsegs TfibB) | exact TfibB_syms | exact FIN.fm_tfib_lib | exact FIN.fm_univ_holds
  | exact FIB.fm_FmB_TfibB | exact FIN.fm_img_facts_TfibB | exact FBC.fm_bcmp_TfibB | exact fmapp_cells
  | exact fmapp_amalloc | exact fmapp_afree | exact fmapp_amemcpy | exact fmapp_amemset
  | apply (FSL.astrlen_holds TfibB) | apply (FSN.fm_snprintf_realizes TfibB) | apply (FSS.fm_astrstr TfibB)
  | apply (FSC.astrncmp_holds TfibB) | apply (FSI.fm_astrncasecmp_realizes TfibB) | apply (FCH.astrchr_holds TfibB)
  | apply (FCT.aisalnum_holds TfibB) | apply (FPW.tfib_poison16 TfibB) | apply (FPW.tfib_unpoison16 TfibB)
  | apply (FAL.fuzz_alloc_live_holds TfibB) | apply (FFL.fuzz_alloc_fail_holds TfibB)
  | apply (FFM.fuzz_malloc_holds TfibB) | apply (FFF.fuzz_free_holds TfibB)
  | solve [reflexivity]
  | solve [cbv [CTX_lv2_locate_manifest_names]; repeat (first [left; reflexivity | right])] ].

(* has_prefixed (lib/B/FMW_has_prefixed.v), with name_char (lib/B/FMW_name_char.v) *)
Lemma fmapp_hasp : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @has_prefixed_spec fx rc tfib_sink_head tfibsegs TfibB.
Proof.
  intros fx rc.
  apply (FHP.has_prefixed_holds TfibB).
  all: first [apply (FNC.name_char_holds TfibB) | fmapp_leaf].
  all: fmapp_leaf.
  all: fmapp_leaf.
Qed.

(* plain (lib/B/FMW_plain.v) *)
Lemma fmapp_plain : forall {fx : YK11.FPState} {rc : YM05.RunCeil}, plain_spec tfibsegs TfibB.
Proof.
  intros fx rc.
  apply (FPL.plain_spec_holds TfibB).
  all: fmapp_leaf.
  all: fmapp_leaf.
Qed.

(* expected (lib/B/FMW_ex_all.v): its bcmp premise is lib/B/FMbcmp.v fm_bcmp_TfibB *)
Lemma fmapp_expected : forall {fx : YK11.FPState} {rc : YM05.RunCeil}, expected_spec tfibsegs TfibB.
Proof.
  intros fx rc.
  apply (FEA.expected_spec_holds TfibB).
  all: first [exact fmapp_plain | fmapp_leaf].
  all: fmapp_leaf.
  all: fmapp_leaf.
Qed.

(* NAMES: names over readings at names' callers; each premise of readings, and of the lemmas proving it, is one of the
   closed B facts above or has_prefixed (fmapp_hasp) *)
Lemma fmapp_names : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @names_spec fx rc tfib_sink_head tfibsegs TfibB CTX_lv2_locate_manifest_names.
Proof.
  intros fx rc.
  apply (FNM.names_holds TfibB CTX_lv2_locate_manifest_names CTX_lv2_locate_manifest_readings).
  - exact fmapp_names_ctx.
  - apply (FRD.readings_holds TfibB CTX_lv2_locate_manifest_readings).
    all: first
      [ exact fmapp_rd_ctx | exact fmapp_cells | exact FIN.fm_img_facts_TfibB | exact fmapp_hasp
      | apply (FFM.fuzz_malloc_holds TfibB) | apply (FFF.fuzz_free_holds TfibB)
      | apply (FSL.astrlen_holds TfibB) | apply (FSN.fm_snprintf_realizes TfibB) | apply (FSS.fm_astrstr TfibB)
      | apply (FSC.astrncmp_holds TfibB) | apply (FSI.fm_astrncasecmp_realizes TfibB)
      | apply (FCH.astrchr_holds TfibB) | apply (FCT.aisalnum_holds TfibB) ].
    all: first
      [ exact (AR_laws_ok tfibsegs TfibB) | exact TfibB_syms | exact FIN.fm_tfib_lib | exact FIN.fm_univ_holds
      | exact fmapp_amalloc | exact fmapp_afree
      | apply (FPW.tfib_poison16 TfibB) | apply (FPW.tfib_unpoison16 TfibB) ].
    all: first [exact (AR_laws_ok tfibsegs TfibB) | exact TfibB_syms].
Qed.

(* the five G5 walks and G6's check_round_trip *)
Lemma fmapp_cno : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_no_overread_spec fx rc tfib_sink_head tfibsegs TfibB CTX_check_no_overread.
Proof.
  intros fx rc.
  apply (FCN.check_no_overread_holds TfibB).
  all: first [exact fmapp_names | fmapp_leaf].
Qed.

Lemma fmapp_cba : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_bounded_alloc_spec fx rc tfib_sink_head tfibsegs TfibB.
Proof. intros fx rc. exact (FCB.check_bounded_alloc_holds TfibB). Qed.

Lemma fmapp_caw : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_as_written_spec fx rc tfib_sink_head tfibsegs TfibB.
Proof. intros fx rc. apply (FCW.check_as_written_holds TfibB). exact fmapp_expected. Qed.

Lemma fmapp_crc : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_reject_clean_spec fx rc tfib_sink_head tfibsegs TfibB.
Proof. intros fx rc. apply (FCR.check_reject_clean_holds TfibB). all: fmapp_leaf. Qed.

Lemma fmapp_starved : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_reject_clean_starved_spec fx rc tfib_sink_head tfibsegs TfibB CTX_check_reject_clean_starved.
Proof.
  intros fx rc.
  apply (FSV.check_reject_clean_starved_holds TfibB CTX_lv2_locate_manifest_names).
  all: first [exact fmapp_names | exact fmapp_ctx_starved | exact fmapp_crc | fmapp_leaf].
  all: fmapp_leaf.
Qed.

Lemma fmapp_as_ruled : forall {fx : YK11.FPState} {rc : YM05.RunCeil}, as_ruled_spec tfibsegs TfibB CTX_as_ruled.
Proof.
  intros fx rc.
  apply (FAS.as_ruled_holds TfibB CTX_lv2_locate_manifest_names).
  all: first [exact fmapp_names | exact fmapp_ctx_as_ruled | exact fmapp_expected | fmapp_leaf].
Qed.

Lemma fmapp_crt : forall {fx : YK11.FPState} {rc : YM05.RunCeil},
  @check_round_trip_spec fx rc tfib_sink_head tfibsegs TfibB CTX_check_round_trip.
Proof.
  intros fx rc.
  apply (FRT.check_round_trip_holds TfibB).
  all: first [exact fmapp_names | exact fmapp_as_ruled | exact fmapp_plain | fmapp_leaf].
  all: fmapp_leaf.
Qed.

(* the walk of LLVMFuzzerTestOneInput at TfibB (lib/B/FMTfibTop.v), what lib/B/FMW_harness.v's WALK assumes *)
Theorem fm_llvmf_walk_holds : OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.fm_llvmf_walk.
Proof.
  intros fx rc.
  exact (llvmf_walk TfibB FIB.fm_FmB_TfibB FIN.fm_img_facts_TfibB FIN.fm_univ_holds fmapp_amalloc fmapp_afree
    fmapp_memchr fmapp_aicpy fmapp_cno (FAL.fuzz_alloc_live_holds TfibB)
    (FAR.fuzz_alloc_peak_reset_holds TfibB TfibB_syms) (FAP.fuzz_alloc_peak_holds TfibB) fmapp_names fmapp_cba
    fmapp_caw fmapp_crc fmapp_starved fmapp_crt).
Qed.

(* fm's two image-B statements, from the walk (lib/B/FMFinal.v over FMTfibTop.fm_TFIB_TB_of_walk and FMTopB.v) *)
Theorem fm_asan_ubsan_agrees_B : OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_ubsan_agrees.
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMFinal.fm_asan_ubsan_agrees_of_walk
    fm_llvmf_walk_holds).
Qed.

Theorem fm_asan_ubsan_halts_B : OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_ubsan_halts.
Proof.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMFinal.fm_asan_ubsan_halts_of_walk
    fm_llvmf_walk_holds).
Qed.
