From Stdlib Require Import ZArith List Arith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import strlen_c strcmp_c bcmp_c memchr_c memset_c memcpy_c put_utf8_c snprintf_c skip_ws_c literal_c strtod_c hex4_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import fuzz_malloc_c fuzz_free_c fuzz_realloc_c fuzz_strdup_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c grow_c parse_string_c parse_value_c parse_items_c put_c indent_c put_string_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strlen strcmp bcmp memchr memset memcpy put_utf8 snprintf skip_ws literal strtod hex4 pj_object pj_get pj_get_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require fuzz_malloc fuzz_free fuzz_realloc fuzz_strdup preset_base64_encode preset_base64_decode grow parse_string pj_string pj_set pj_free pj_parse put indent put_string write_value pj_write.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF FrameFactsCG.
Import ListNotations.
Local Open Scope Z_scope.

(* The callee contracts of check_round_trip (ubsan build), from the proved X_holds theorems and frame_facts_ubsan
   (frame_allocator for the allocator facts), the same 16 conjuncts as crt_callees_plain (Prog/CrtCallees.v).
   No theorem proves the parse_value or the parse_items step at the ubsan addresses yet: each is one premise below,
   and the depth induction of ParseUnit.parse_unit (plain) combines them into parse_value at depth 0 for pj_parse. *)

(* Needed by crt_callees_ubsan for pj_parse_contract: the parse_items step, for every B API of the frame. *)
Definition parse_items_step_ubsan : Prop :=
  forall (B : malloc_syms) (API : forall rc : YM05.RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall (rc : YM05.RunCeil) (d : nat),
    ((d < MAXD)%nat -> forall fx : YK11.FPState, parse_value_contract (fx := fx) B (API rc) sb_form (S d)) ->
    (forall fx : YK11.FPState, grow_contract (fx := fx) B (API rc) sb_form) ->
    (forall fx : YK11.FPState, parse_string_contract (fx := fx) B (API rc) sb_form) ->
    memset_contract -> skip_ws_contract ->
    (forall fx : YK11.FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form) ->
    forall fx : YK11.FPState, parse_items_contract (fx := fx) B (API rc) sb_form d.

(* Needed by crt_callees_ubsan for pj_parse_contract: the parse_value step, for every B API of the frame. *)
Definition parse_value_step_ubsan : Prop :=
  forall (B : malloc_syms) (API : forall rc : YM05.RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall (rc : YM05.RunCeil) (d : nat),
    (forall fx : YK11.FPState, parse_items_contract (fx := fx) B (API rc) sb_form d) ->
    (forall fx : YK11.FPState, parse_string_contract (fx := fx) B (API rc) sb_form) ->
    literal_contract -> skip_ws_contract ->
    (forall fx : YK11.FPState, fuzz_malloc_contract (fx := fx) B (API rc) sb_form) ->
    memcpy_contract -> strtod_contract ->
    forall fx : YK11.FPState, parse_value_contract (fx := fx) B (API rc) sb_form d.

Theorem crt_callees_ubsan : parse_items_step_ubsan -> parse_value_step_ubsan ->
  forall (B : malloc_syms) (API : forall rc : YM05.RunCeil, AllocAPI B) (LS : lib_shape)
    (SH : sink_head) (SK : sink_syms) (empty : Z),
    frame_facts_cg B API LS SH SK empty -> forall rc : YM05.RunCeil,
    strlen_contract /\ strcmp_contract /\ bcmp_contract /\ pj_object_contract /\ pj_get_contract /\
    pj_get_str_contract /\
    (forall fx : YK11.FPState, malloc_contract (fx := fx) B (API rc)) /\
    (forall fx : YK11.FPState, free_contract (fx := fx) B (API rc)) /\
    (forall fx : YK11.FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, preset_base64_encode_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, preset_base64_decode_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, pj_string_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, pj_set_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, pj_free_contract (fx := fx) B (API rc) sb_form) /\
    (forall fx : YK11.FPState, pj_write_contract_sb (fx := fx) B (API rc)) /\
    (forall fx : YK11.FPState, pj_parse_contract (fx := fx) B (API rc) sb_form).
Proof.
  intros PI PV B API LS SH SK empty FF rc.
  pose proof (PI B API LS SH SK empty FF rc) as PIc. pose proof (PV B API LS SH SK empty FF rc) as PVc.
  destruct FF as (SEG & MAL & FRE & REA & _ & ERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & GFR & _ & _ & _ & _ & FA).
  specialize (ERR rc).
  destruct (FA rc YK11.fx0) as (_ & _ & _ & _ & _ & BSP & CO & _ & _ & _ & _ & _ & _ & AX & GO & _).
  pose proof (fuzz_malloc.omx_globals_free (fx := YK11.fx0) B (API rc) SEG AX GO GFR) as GOMX.
  pose proof strlen.strlen_holds as SL. pose proof strcmp.strcmp_holds as SC. pose proof bcmp.bcmp_holds as BC.
  pose proof memchr.memchr_holds as MCH. pose proof memset.memset_holds as MS. pose proof memcpy.memcpy_holds as MC.
  pose proof put_utf8.put_utf8_holds as PU. pose proof snprintf.snprintf_holds as SNP.
  pose proof strtod.strtod_holds as STD. pose proof hex4.hex4_holds as HX. pose proof skip_ws.skip_ws_holds as SKW.
  pose proof (literal.literal_holds SL BC) as LIT.
  pose proof (pj_get.pj_get_holds SC) as PG.
  assert (MALL : forall fx : YK11.FPState, malloc_contract (fx := fx) B (API rc))
    by (intros fx; exact (proj1 (FA rc fx))).
  assert (FREE : forall fx : YK11.FPState, free_contract (fx := fx) B (API rc))
    by (intros fx; exact (proj1 (proj2 (FA rc fx)))).
  assert (REAL : forall fx : YK11.FPState, realloc_contract_r (fx := fx) B (API rc) sb_form 0x184e8)
    by (intros fx; exact (proj1 (proj1 (proj2 (proj2 (proj2 (FA rc fx)))) 0x184e8 REA))).
  assert (FM : forall fx : YK11.FPState, fuzz_malloc_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_malloc.fuzz_malloc_holds (fx := fx)); first [assumption | exact (MALL fx)]. }
  assert (FFR : forall fx : YK11.FPState, fuzz_free_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_free.fuzz_free_holds (fx := fx)); first [assumption | exact (FREE fx)]. }
  assert (FR : forall fx : YK11.FPState, fuzz_realloc_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (fuzz_realloc.fuzz_realloc_holds (fx := fx) B (API rc) SEG ERR GOMX sb_form (REAL fx) (FM fx)). }
  assert (FS : forall fx : YK11.FPState, fuzz_strdup_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (fuzz_strdup.fuzz_strdup_holds (fx := fx)); first [assumption | exact (FM fx)]. }
  assert (GROW : forall fx : YK11.FPState, grow_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (grow.grow_holds (fx := fx) B (API rc) sb_form AX (FR fx)). }
  assert (PSTR : forall fx : YK11.FPState, parse_string_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (parse_string.parse_string_holds (fx := fx) B (API rc) sb_form AX CO (FM fx) (FFR fx) PU HX). }
  assert (PJF : forall fx : YK11.FPState, pj_free_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (pj_free.pj_free_holds (fx := fx)); first [assumption | exact (FFR fx)]. }
  (* The depth induction of ParseUnit.parse_unit, from MAXD down to 0. *)
  assert (PVk : forall k, (k <= MAXD)%nat ->
    forall fx : YK11.FPState, parse_value_contract (fx := fx) B (API rc) sb_form (MAXD - k)).
  { induction k as [|k IH]; intros Hk.
    - apply (PVc _); [|exact PSTR | exact LIT | exact SKW | exact FM | exact MC | exact STD].
      apply (PIc _); [intros Hlt; exfalso; lia | exact GROW | exact PSTR | exact MS | exact SKW | exact FFR].
    - apply (PVc _); [|exact PSTR | exact LIT | exact SKW | exact FM | exact MC | exact STD].
      apply (PIc _); [|exact GROW | exact PSTR | exact MS | exact SKW | exact FFR].
      intros _. replace (S (MAXD - S k)) with (MAXD - k)%nat by lia. apply IH. lia. }
  assert (PV0 : forall fx : YK11.FPState, parse_value_contract (fx := fx) B (API rc) sb_form 0).
  { intros fx. pose proof (PVk MAXD (le_n _) fx) as H0. rewrite Nat.sub_diag in H0. exact H0. }
  assert (PUT : forall fx : YK11.FPState, put_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (put.put_holds (fx := fx) B (API rc) sb_form (FR fx) MC). }
  assert (IND : forall fx : YK11.FPState, indent_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (indent.indent_holds (fx := fx)); first [assumption | exact (PUT fx)]. }
  assert (PST : forall fx : YK11.FPState, put_string_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (put_string.put_string_holds (fx := fx) B (API rc) sb_form AX CO PUT SNP SL). }
  assert (WV : forall fx : YK11.FPState, write_value_contract (fx := fx) B (API rc) sb_form).
  { intros fx. exact (write_value.write_value_holds (fx := fx) B (API rc) sb_form AX CO PUT IND PST SL BSP). }
  assert (PJW : forall fx : YK11.FPState, pj_write_contract (fx := fx) B (API rc) sb_form).
  { intros fx. apply (pj_write.pj_write_holds (fx := fx)); first [assumption | exact (WV fx)]. }
  split; [exact SL|]. split; [exact SC|]. split; [exact BC|].
  split; [exact (pj_object.pj_object_holds MS)|].
  split; [exact PG|].
  split; [exact (pj_get_str.pj_get_str_holds PG)|].
  split; [exact MALL|]. split; [exact FREE|]. split; [exact FFR|].
  split; [intros fx; exact (preset_base64_encode.preset_base64_encode_holds (fx := fx) B (API rc) sb_form (FM fx))|].
  split; [intros fx; exact (preset_base64_decode.preset_base64_decode_holds (fx := fx) B (API rc) sb_form SL MCH
    (FM fx) (FFR fx) AX CO)|].
  split; [intros fx; apply (pj_string.pj_string_holds (fx := fx)); first [assumption | exact (FS fx)]|].
  split; [intros fx; exact (pj_set.pj_set_holds (fx := fx) B (API rc) sb_form AX PG MC MS (PJF fx) (GROW fx) (FS fx))|].
  split; [exact PJF|].
  split; [intros fx; exact (pj_write.pj_write_sb (fx := fx) B (API rc) (PJW fx))|].
  intros fx. exact (pj_parse.pj_parse_holds (fx := fx) B (API rc) sb_form SKW MS (PV0 fx) PJF).
Qed.

Print Assumptions crt_callees_ubsan.
