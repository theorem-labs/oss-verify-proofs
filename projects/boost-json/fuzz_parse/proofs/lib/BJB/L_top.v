(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib CXXLib2 AsObj AsStack0 AsWalk N8Kit Fuzz_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJIface BJIfaceStr BJIfaceObj BJIfaceObjL BJIfaceTop BJIfaceEsc BJIfaceKey.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import
     L_parse_value
     L_alit_null L_alit_true L_alit_false
     L_bnum0 L_bnumneg
     L_agrow_one L_push_array L_aparr
     L_octor1 L_octor L_octorLD L_octorL1 L_octorL2 L_octorL3 L_apobj L_apobject
     L_pdoc L_wsome L_afuzz L_afuzz_top
     L_adtor_value L_adtor_vs L_ajparse1 L_ajparse2
     L_apchars L_apstr L_apush_key L_apstring L_apkey L_bnumpos L_ftr L_avsgrow L_bpesc5.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJIfaceStr~~~~~~0fpush_chars_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJIfaceEsc~~~~~~l2h2parse_escaped_stmt0h0push_string_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJIface~~~~~~rch1parse_string_stmtrch1parse_numpos_stmt37Corelib4Init5Logichi43andrch0dtor_value_tr_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJBaBJIfaceTop~~~~~~hl3cjparse_tr_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt~~~~~~hq4afuzz_tr_okrch0push_object_stmtrcfpush_array_stmt37Corelib7Numbers7BinNumsih71Zrch2parse_array_stmt_drch2parse_value_stmt_d46Stdlib6ZArith6BinInt1Zim12leim12ltrch3parse_object_stmt_drch0parse_array_stmtrch1parse_object_stmtrch0parse_value_stmthl3awsome_stmthq49fuzz_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~iv43asriv4casan_rt_hyps" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!jj1$0").
  Hypothesis RT : ltac2:(zQ "10!jj8@2$0?5HCEIL?1H").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma PCH : ltac2:(zQ "10!k1@2$0?5HCEIL?1H").           Proof. exact (push_chars_spec H RT). Qed.
  Lemma VSG : vs_grow_stmt H.              Proof. exact (vs_grow_spec H RT). Qed.
  Lemma PESC : ltac2:(zQ "10!p3@2$0?5HCEIL?1H").       (* [comment removed for export] *)
  Proof. exact (parse_escaped_spec H RT PCH VSG). Qed.
  Lemma PSTRL : ltac2:(zQ "10!q9@2$0?5HCEIL?1H").        Proof. exact (push_string_spec H RT). Qed.
  Lemma PKEY : push_key_stmt H.            Proof. exact (push_key_spec H RT). Qed.
  Lemma PS : ltac2:(zQ "10!va@2$0?5HCEIL?1H").          (* [comment removed for export] *)
  Proof. exact (parse_astring_spec H RT PCH PSTRL PESC). Qed.
  Lemma PK : parse_key_stmt H.             (* [comment removed for export] *)
  Proof. exact (parse_akey_spec H RT PCH PKEY PESC). Qed.
  Lemma PNP : ltac2:(zQ "10!hgf@2$0?5HCEIL?1H").         (* [comment removed for export] *)
  Proof. exact (parse_bnumpos_spec H RT). Qed.
  (* [comment removed for export] *)
  Lemma DV : dtor_value_stmt H.          (* [comment removed for export] *)
  Proof. exact (dtor_value_spec H RT). Qed.
  Lemma DSTR : dtor_str_stmt H.            (* [comment removed for export] *)
  Proof. exact (dtor_str_spec H RT). Qed.
  Lemma DARR : dtor_arr_stmt H.
  Proof. exact (dtor_arr_spec H RT). Qed.
  Lemma DOBJ : dtor_obj_stmt H.
  Proof. exact (dtor_obj_spec H RT). Qed.
  Lemma DVS : dtor_vs_stmt H.              (* [comment removed for export] *)
  Proof. exact (dtor_vs_spec H RT (dtor_item_spec H RT)). Qed.
  Lemma FTR_EQ : ltac2:(zQ "40!hj8!hjf!hp4!hu3>0@1$3?1H@2$0@1$2?1H@1$1?1H").   (* [comment removed for export] *)
  Proof. exact (ftr_eq HCEIL H). Qed.

  (* [comment removed for export] *)
  Lemma pobj_all : ltac2:(zQ "10!hv1@2$0?5HCEIL?1H").        (* [comment removed for export] *)
  Proof. exact (push_object_spec H RT DV DSTR DARR DOBJ). Qed.
  Lemma parr_all : ltac2:(zQ "10!ig5@2$0?5HCEIL?1H").         (* [comment removed for export] *)
  Proof. exact (push_array_spec H RT). Qed.
  Lemma PA_STEP : ltac2:(zQ "60!ij0!hj8!ij5!ikb!in9!inf>1d$0>0>2d'$0>0@2$1@2$4Z^1@2$5^1^2@3$3?5HCEIL?1H^2@3$2?5HCEIL?1H^2").    (* [comment removed for export] *)
  Proof. intros d PV. exact (L_aparr.PA_STEP H RT parr_all d PV). Qed.
  Lemma PO_STEP : ltac2:(zQ "60!ij0!hj8!io5!ikb!in9!inf>1d$0>0>2d'$0>0@2$1@2$4Z^1@2$5^1^2@3$3?5HCEIL?1H^2@3$2?5HCEIL?1H^2").   (* [comment removed for export] *)
  Proof. intros d PV. exact (L_apobject.PO_STEP H RT pobj_all PK d PV). Qed.

  (* [comment removed for export] *)
  Lemma parse_family : ltac2:(zQ "40!hj8!ipc!ir0!is5@2$0@2$3?5HCEIL?1H@2$0@2$1?5HCEIL?1H@2$2?5HCEIL?1H").
  Proof.
    apply (parse_family_by_depth H).
    - exact PA_STEP.
    - exact PO_STEP.
    - intros d PA PO. exact (PV_STEP H RT d PA PO PS (parse_bnum0_spec H RT) (parse_bnumneg_spec H RT) PNP
                               (parse_null_spec H RT) (parse_true_spec H RT) (parse_false_spec H RT)).
  Qed.

  Lemma parse_value_all : ltac2:(zQ "10!is5@2$0?5HCEIL?1H").
  Proof. exact (proj1 parse_family). Qed.

  (* [comment removed for export] *)
  Lemma pdoc_all : pdoc_stmt H.
  Proof. exact (pdoc_spec H RT parse_value_all). Qed.

  Lemma wsome_all : ltac2:(zQ "10!it9@2$0?5HCEIL?1H").
  Proof. exact (wsome_spec H RT pdoc_all). Qed.

  Lemma JP : jparse_stmt H.                (* [comment removed for export] *)
  Proof. exact (ajparse_spec H RT wsome_all DVS). Qed.

  Theorem fuzz_all : ltac2:(zQ "10!iu7@2$0?5HCEIL?1H").
  Proof. exact (afuzz_spec H RT JP DV FTR_EQ). Qed.
End W.
