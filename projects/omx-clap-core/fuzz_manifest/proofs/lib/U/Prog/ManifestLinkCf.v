From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require
  strlen fuzz_malloc ManifestB ManifestLink
  fuzz_malloc_c_cf fuzz_malloc_cf fuzz_free_c_cf fuzz_free_cf readings_c_cf readings_cf names_c_cf names_cf
  as_ruled_c_cf as_ruled_cf check_reject_clean_starved_c_cf check_reject_clean_starved_cf
  check_no_overread_c_cf check_no_overread_cf check_round_trip_c_cf check_round_trip_cf
  StatementUbsanCg ManifestFFCg.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Reusable Require Import YK11 YM05 YO0d YO0f YO09 YP09 YL0g YL0i YL01 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Contract FrameAPI SlotAgree.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Img0.
Import ListNotations.
Local Open Scope Z_scope.

(* The cut-free callee bundle of fuzz_manifest's ubsan slot, mirroring ManifestLink.v's section Link: at an agreement
   frame (StatementUbsanCg.frame_facts_cg with the cut-free allocator contracts and LIMLAW), the cut-free contracts of
   the allocating callees from their *_cf_holds theorems. The Kind A contracts are ManifestLink.v's. *)
Section LinkCf.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z).
Hypothesis FF : StatementUbsanCg.frame_facts_cg B API LS SH SK ra empty.
Hypothesis MCF : forall fx : FPState, @malloc_contract_cf fx rc B (API rc).
Hypothesis FCF : forall fx : FPState, @free_contract_cf fx rc B (API rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (API rc) L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).

Lemma lkc_segs : ms_segs B = Img0.rsegs.
Proof.
  pose proof FF as F. unfold StatementUbsanCg.frame_facts_cg in F.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma lkc_frame_G_free (fx : FPState) :
  forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof.
  pose proof (@ManifestFFCg.ffc_allocator fx rc B API LS SH SK ra empty FF) as FA. unfold frame_allocator in FA.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a |- _ =>
    exact H end.
Qed.

Lemma lkc_errno_low : ManifestB.errno_low B.
Proof. exact (@ManifestFFCg.ffc_errno_low rc B API LS SH SK ra empty FF). Qed.

Lemma Lc_fuzz_malloc : forall fx : FPState, @fuzz_malloc_c_cf.fuzz_malloc_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@fuzz_malloc_cf.fuzz_malloc_cf_holds fx rc B (API rc) lkc_segs
           (proj1 (ManifestFFCg.ffc_malloc_syms_omx B API LS SH SK ra empty FF)) lkc_errno_low
           (@fuzz_malloc.omx_globals_free fx rc B (API rc) lkc_segs
              (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF) (lkc_frame_G_free fx)
              (ManifestFFCg.ffc_globals B API LS SH SK ra empty FF))
           MCF LIMLAW).
Qed.

Lemma Lc_fuzz_free : forall fx : FPState, @fuzz_free_c_cf.fuzz_free_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@fuzz_free_cf.fuzz_free_cf_holds fx rc B (API rc) lkc_segs
           (proj2 (ManifestFFCg.ffc_malloc_syms_omx B API LS SH SK ra empty FF))
           (ManifestFFCg.ffc_globals B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF) (lkc_frame_G_free fx)
           FCF).
Qed.

Lemma Lc_readings : forall fx : FPState, @readings_c_cf.readings_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@readings_cf.readings_cf_holds fx rc B (API rc)
           (@ManifestFFCg.ffc_statics_free fx rc B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_ctx_owned fx rc B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_block_slack_present fx rc B API LS SH SK ra empty FF)
           lkc_errno_low (ManifestFFCg.ffc_guard_syms B API LS SH SK ra empty FF)
           ManifestLink.L_strlen ManifestLink.L_strncmp ManifestLink.L_strncasecmp ManifestLink.L_strchr
           ManifestLink.L_isalnum ManifestLink.L_has_prefixed ManifestLink.L_snprintf ManifestLink.L_strstr
           Lc_fuzz_malloc Lc_fuzz_free).
Qed.

Lemma Lc_names : forall fx : FPState, @names_c_cf.names_contract_cf fx rc B (API rc).
Proof. intros fx. exact (@names_cf.names_cf_holds fx rc B (API rc) lkc_errno_low Lc_readings). Qed.

Lemma Lc_as_ruled : forall fx : FPState, @as_ruled_c_cf.as_ruled_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@as_ruled_cf.as_ruled_cf_holds fx rc B (API rc) lkc_errno_low
           (ManifestFFCg.ffc_guard_syms B API LS SH SK ra empty FF) Lc_names ManifestLink.L_expected).
Qed.

Lemma Lc_check_reject_clean_starved :
  forall fx : FPState, @check_reject_clean_starved_c_cf.check_reject_clean_starved_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_reject_clean_starved_cf.check_reject_clean_starved_cf_holds fx rc B (API rc) lkc_errno_low
           (@ManifestFFCg.ffc_statics_free fx rc B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_guard_syms B API LS SH SK ra empty FF)
           ManifestLink.L_fuzz_alloc_live ManifestLink.L_fuzz_alloc_fail Lc_names ManifestLink.L_check_reject_clean).
Qed.

Lemma Lc_check_no_overread :
  forall fx : FPState, @check_no_overread_c_cf.check_no_overread_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_no_overread_cf.check_no_overread_cf_holds fx rc B (API rc)
           (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_ctx_owned fx rc B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_statics_free fx rc B API LS SH SK ra empty FF)
           lkc_errno_low (ManifestFFCg.ffc_statics_noerrno B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_malloc_syms_omx B API LS SH SK ra empty FF)
           MCF FCF ManifestLink.L_memcpy ManifestLink.L_memset Lc_names LIMLAW).
Qed.

Lemma Lc_check_round_trip :
  forall fx : FPState, @check_round_trip_c_cf.check_round_trip_contract_cf fx rc B (API rc).
Proof.
  intros fx.
  exact (@check_round_trip_cf.check_round_trip_cf_holds fx rc B (API rc) Lc_names Lc_as_ruled MCF FCF LIMLAW
           ManifestLink.L_snprintf strlen.strlen_holds ManifestLink.L_plain
           (ManifestFFCg.ffc_statics_facts B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_statics_free fx rc B API LS SH SK ra empty FF)
           lkc_errno_low
           (@ManifestFFCg.ffc_ctx_owned fx rc B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_guard_syms B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_statics_noerrno B API LS SH SK ra empty FF)
           (ManifestFFCg.ffc_malloc_syms_omx B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_alloc_extra fx rc B API LS SH SK ra empty FF)
           (@ManifestFFCg.ffc_block_slack_present fx rc B API LS SH SK ra empty FF)).
Qed.

End LinkCf.
