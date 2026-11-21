(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_infl_iface Zg_infl_iface Zg_infl_t_iface Zg_infl_arms Zg_infl_a_lit Zg_infl_a_term Zg_infl_a_type Zg_infl_a_dict Zg_infl_a_dictid Zg_infl_a_head Zg_infl_a_match Zg_infl_a_distext Zg_infl_a_dist Zg_infl_a_lenext Zg_infl_a_len Zg_infl_a_lenfast Zg_infl_a_table Zg_infl_a_lenlens Zg_infl_a_codelens Zg_infl_a_check Zg_infl_a_stored Zg_infl_a_copy.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface InflateState InflateArms Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Open.
  Variable flush : Z.
  Hypothesis RF : 0 <= flush <= 4.
  Hypothesis ITABLE : inflate_table_stmt.
  Hypothesis INFFAST : inflate_fast_stmt.
  Hypothesis ADLER32 : adler32_stmt.

  (* [comment removed for export] *)
  Let MATCH_CORE : match_core_stmt := match_core.
  Let DISTEXT_CORE : distext_core_stmt := distext_core MATCH_CORE.
  Let DIST_CORE : dist_core_stmt := dist_core DISTEXT_CORE.
  Let LENEXT_ON : lenext_core_on_stmt := lenext_core_on DIST_CORE.
  Let LENEXT_OFF : lenext_core_off_stmt := lenext_core_off DIST_CORE.
  Let LEN_FAST : len_fast_stmt := len_fast INFFAST.
  Let LEN_CORE : len_core_stmt := len_core LENEXT_ON LENEXT_OFF LEN_FAST.
  Let LEN__CORE : len__core_stmt := len__core LENEXT_ON LENEXT_OFF LEN_FAST.
  Let CODELENS_CORE : codelens_core_stmt flush := codelens_core flush ITABLE RF LEN__CORE.
  Let LENLENS_CORE : lenlens_core_stmt flush := lenlens_core flush CODELENS_CORE ITABLE.

  Lemma arms_okg_of : arms_okg flush.
  Proof.
    constructor.
    - exact (arm_HEAD_ok flush).
    - exact (arm_DICTID_ok flush RF).
    - exact (arm_DICT_ok flush RF).
    - exact (arm_TYPE_ok flush RF).
    - exact (arm_TYPEDO_ok flush RF).
    - exact (arm_STORED_of copy__core_ok flush RF).
    - exact (arm_COPY__ok flush).
    - exact (arm_COPY_ok flush).
    - exact (arm_TABLE_of flush LENLENS_CORE).
    - exact (arm_LENLENS_of flush CODELENS_CORE ITABLE).
    - exact (arm_CODELENS_of flush ITABLE RF LEN__CORE).
    - exact (arm_LEN__of LENEXT_ON LENEXT_OFF LEN_FAST flush).
    - exact (arm_LEN_of LENEXT_ON LENEXT_OFF LEN_FAST flush).
    - exact (arm_LENEXT_of DIST_CORE flush).
    - exact (arm_DIST_of DISTEXT_CORE flush).
    - exact (arm_DISTEXT_of MATCH_CORE flush).
    - exact (arm_MATCH_ok flush).
    - exact (arm_LIT_ok flush).
    - exact (arm_CHECK_of ADLER32 flush).
    - exact (arm_LENGTH_ok flush).
    - exact (arm_DONE_ok flush).
    - exact (arm_BAD_ok flush).
    - exact (arm_MEM_ok flush).
  Qed.
End Open.
