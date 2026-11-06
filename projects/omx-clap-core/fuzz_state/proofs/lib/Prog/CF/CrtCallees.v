From Stdlib Require Import ZArith List Arith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c memchr_c memset_c memcpy_c put_utf8_c snprintf_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import fuzz_malloc_c fuzz_free_c fuzz_realloc_c fuzz_strdup_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c grow_c parse_string_c parse_value_c parse_items_c put_c indent_c put_string_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require literal_c strtod_c hex4_c strlen strcmp bcmp memchr memset memcpy put_utf8 snprintf literal strtod hex4 pj_object.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require fuzz_malloc fuzz_free fuzz_realloc fuzz_strdup preset_base64_encode preset_base64_decode ReaderLink put indent put_string write_value pj_write.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF FrameFactsCG.
Import ListNotations.
Local Open Scope Z_scope.

(* The callee contracts of check_round_trip (plain build), from the proved X_holds theorems and frame_facts_plain
   (frame_allocator for the allocator facts), in the order of the premises of St8 (check_round_trip_st8.v).
   The one premise no theorem proves yet is the parse_items step of ParseUnit.parse_unit (reader_link), at sb_form. *)

(* Needed by crt_callees_plain for the reader's contracts: the parse_items step, for every B API of the frame. *)
Definition parse_items_step_plain : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall (rc : RunCeil) (d : nat),
    ((d < MAXD)%nat -> forall fx : FPState, parse_value_contract (fx := fx) B (API rc) sb_form (S d)) ->
    (forall fx : FPState, grow_contract (fx := fx) B (API rc) sb_form) ->
    (forall fx : FPState, parse_string_contract (fx := fx) B (API rc) sb_form) ->
    memset_contract ->
    (forall fx : FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form) ->
    forall fx : FPState, parse_items_contract (fx := fx) B (API rc) sb_form d.

Theorem crt_callees_plain : parse_items_step_plain ->
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall rc : RunCeil,
    strlen_contract /\ strcmp_contract /\ bcmp_contract /\ pj_object_contract /\ pj_get_contract /\
    pj_get_str_contract /\
    (forall fx : FPState, malloc_contract (fx := fx) B (API rc)) /\
    (forall fx : FPState, free_contract (fx := fx) B (API rc)) /\
    (forall fx : FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, preset_base64_encode_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, preset_base64_decode_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, pj_string_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, pj_set_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, pj_free_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : FPState, pj_write_contract_sb (fx := fx) B (API rc)) /\
    (forall fx : FPState, pj_parse_contract (fx := fx) B (API rc) sb_form).
Proof.
  intros PI B API LS SH SK empty FF rc.
  pose proof (PI B API LS SH SK empty FF rc) as PIc.
  destruct FF as (SEG & MAL & FRE & REA & _ & ERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & GFR & _ & _ & _ & _ & FA).
  specialize (ERR rc).
  destruct (FA rc YK11.fx0) as (_ & _ & _ & _ & _ & BSP & CO & _ & _ & _ & EU & _ & _ & AX & GO & _).
  pose proof (fuzz_malloc.omx_globals_free (fx := YK11.fx0) B (API rc) SEG AX GO GFR) as GOMX.
  pose proof strlen.strlen_holds as SL. pose proof strcmp.strcmp_holds as SC. pose proof bcmp.bcmp_holds as BC.
  pose proof memchr.memchr_holds as MCH. pose proof memset.memset_holds as MS. pose proof memcpy.memcpy_holds as MC.
  pose proof put_utf8.put_utf8_holds as PU. pose proof snprintf.snprintf_holds as SNP.
  pose proof strtod.strtod_holds as STD. pose proof hex4.hex4_holds as HX.
  pose proof (literal.literal_holds SL BC) as LIT.
  assert (MALL : forall fx : FPState, malloc_contract (fx := fx) B (API rc)) by (intros fx; exact (proj1 (FA rc fx))).
  assert (FREE : forall fx : FPState, free_contract (fx := fx) B (API rc))
    by (intros fx; exact (proj1 (proj2 (FA rc fx)))).
  assert (REAL : forall fx : FPState, realloc_contract_r (fx := fx) B (API rc) sb_form 0x17e00)
    by (intros fx; exact (proj1 (proj1 (proj2 (proj2 (proj2 (FA rc fx)))) 0x17e00 REA))).
  assert (FM : forall fx : FPState, fuzz_malloc_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_malloc.fuzz_malloc_holds (fx := fx)); first [assumption | exact (MALL fx)]. }
  assert (FFR : forall fx : FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_free.fuzz_free_holds (fx := fx)); first [assumption | exact (FREE fx)]. }
  assert (FR : forall fx : FPState, fuzz_realloc_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (fuzz_realloc.fuzz_realloc_holds (fx := fx) B (API rc) SEG ERR GOMX sb_form (REAL fx) (FM fx)). }
  assert (FS : forall fx : FPState, fuzz_strdup_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_strdup.fuzz_strdup_holds (fx := fx)); first [assumption | exact (FM fx)]. }
  pose proof (ReaderLink.reader_link B (API rc) sb_form AX CO EU FM FFR FR FS MS MC STD SC LIT PU HX) as RD.
  assert (PUT : forall fx : FPState, put_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (put.put_holds (fx := fx) B (API rc) sb_form (FR fx) MC). }
  assert (IND : forall fx : FPState, indent_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (indent.indent_holds (fx := fx)); first [assumption | exact (PUT fx)]. }
  assert (PST : forall fx : FPState, put_string_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (put_string.put_string_holds (fx := fx) B (API rc) sb_form AX CO PUT SNP SL). }
  assert (WV : forall fx : FPState, write_value_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (write_value.write_value_holds (fx := fx) B (API rc) sb_form AX CO PUT IND PST SL BSP). }
  assert (PJW : forall fx : FPState, pj_write_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (pj_write.pj_write_holds (fx := fx)); first [assumption | exact (WV fx)]. }
  split; [exact SL|]. split; [exact SC|]. split; [exact BC|].
  split; [exact (pj_object.pj_object_holds MS)|].
  split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (RD YK11.fx0))))))|].
  split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (RD YK11.fx0)))))))|].
  split; [exact MALL|]. split; [exact FREE|]. split; [exact FFR|].
  split; [intros fx; exact (preset_base64_encode.preset_base64_encode_holds (fx := fx) B (API rc) sb_form (FM fx))|].
  split; [intros fx; exact (preset_base64_decode.preset_base64_decode_holds (fx := fx) B (API rc) sb_form SL MCH
    (FM fx) (FFR fx) AX CO)|].
  split; [intros fx; exact (proj1 (proj2 (proj2 (RD fx))))|].
  split; [intros fx; exact (proj1 (proj2 (proj2 (proj2 (RD fx)))))|].
  split; [intros fx; exact (proj1 (proj2 (RD fx)))|].
  split; [intros fx; exact (pj_write.pj_write_sb (fx := fx) B (API rc) (PJW fx))|].
  intros fx. exact (proj1 (RD fx)).
Qed.

Print Assumptions crt_callees_plain.
