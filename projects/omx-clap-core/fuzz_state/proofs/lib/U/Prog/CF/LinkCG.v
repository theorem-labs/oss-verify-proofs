From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memchr_c memcpy_c memset_c strlen_c bcmp_c fuzz_alloc_live_c fuzz_alloc_peak_c fuzz_alloc_peak_reset_c fuzz_alloc_fail_c check_bounded_alloc_c check_reject_clean_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import LLVMFuzzerTestOneInput check_no_overread_c check_as_written_c check_round_trip_c check_reject_clean_starved_c past_nul_c fuzz_malloc_c fuzz_free_c preset_base64_decode_c preset_base64_encode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memchr memcpy memset strlen bcmp fuzz_alloc_live fuzz_alloc_peak fuzz_alloc_peak_reset fuzz_alloc_fail check_bounded_alloc check_reject_clean.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import check_no_overread check_as_written check_reject_clean_starved past_nul fuzz_malloc fuzz_free preset_base64_decode preset_base64_encode.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require check_round_trip check_round_trip_stages_b CrtCallees parse_items parse_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF FrameFactsCG.
Import ListNotations.
Local Open Scope Z_scope.

(* U/Prog/Link.v in the cut-free universe: the slot's callee contracts from the cut-free X_holds theorems with their
   premises from frame_facts_cg, check_round_trip's from its cut-free proof and CrtCallees, the reader steps from
   parse_items_step / parse_value_step; then the cut-free slot of the agreement statement (slot_premise_cg). *)

Definition check_round_trip_cg : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_cg B API LS SH SK empty ->
    forall (rc : RunCeil) (fx : FPState), check_round_trip_contract B (API rc).

Ltac link_disch :=
  first [ assumption | exact memchr_holds | exact memcpy_holds | exact memset_holds | exact strlen_holds
        | exact bcmp_holds | exact fuzz_alloc_live_holds | exact fuzz_alloc_fail_holds ].

Theorem slot_callees_cg_of : check_round_trip_cg -> slot_callees_ubsan.
Proof.
  intros CRT B API LS SH SK empty FF rc fx.
  pose proof (CRT B API LS SH SK empty FF rc fx) as CRTc.
  destruct FF as (SEG & MAL & FRE & _ & _ & ERR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & GFR & _ & _ & _ & _ & FA).
  specialize (ERR rc).
  destruct (FA rc fx) as (MALLOC & FREE & _ & _ & _ & BSP & CO & _ & _ & _ & _ & _ & _ & AX & GO & _).
  pose proof (fuzz_free.ff_globals_free B (API rc) SEG GFR AX GO) as GF.
  pose proof (fuzz_malloc.omx_globals_free B (API rc) SEG AX GO GFR) as GOMX.
  assert (FM : fuzz_malloc_contract B (API rc) sb_form) by (apply fuzz_malloc_holds; link_disch).
  assert (FFR : fuzz_free_contract B (API rc) sb_form) by (apply fuzz_free_holds; link_disch).
  assert (DEC : preset_base64_decode_contract B (API rc) sb_form) by (apply preset_base64_decode_holds; link_disch).
  assert (ENC : preset_base64_encode_contract B (API rc) sb_form) by (apply preset_base64_encode_holds; link_disch).
  assert (PN : past_nul_contract B (API rc)) by (apply past_nul_holds; link_disch).
  assert (CRC : check_reject_clean_contract) by (apply check_reject_clean_holds; link_disch).
  unfold slot_callees.
  split; [exact memchr_holds|].
  split; [exact memcpy_holds|].
  split; [exact fuzz_alloc_live_holds|].
  split; [exact fuzz_alloc_peak_reset_holds|].
  split; [exact fuzz_alloc_peak_holds|].
  split; [exact check_bounded_alloc_holds|].
  split; [exact CRC|].
  split; [apply check_no_overread_holds; link_disch|].
  split; [exact DEC|].
  split; [apply check_as_written_holds; link_disch|].
  split; [exact CRTc|].
  split; [apply check_reject_clean_starved_holds; link_disch|].
  exact FFR.
Qed.

Theorem check_round_trip_cg_of : CrtCallees.parse_items_step_ubsan -> CrtCallees.parse_value_step_ubsan -> check_round_trip_cg.
Proof.
  intros PI PV B API LS SH SK empty FF rc fx.
  pose proof (CrtCallees.crt_callees_ubsan PI PV B API LS SH SK empty FF rc) as CAL.
  destruct FF as (SEG & MAL & FRE & _ & _ & ERR & GRD & GGD & _ & _ & _ & _ & _ & _ & _ & TP & EOFF & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & GFR & _ & _ & _ & _ & FA).
  specialize (ERR rc).
  destruct (FA rc fx) as (MALLOC & FREE & _ & _ & _ & BSP & CO & _ & _ & _ & _ & _ & _ & AX & GO & _).
  pose proof (fuzz_free.ff_globals_free B (API rc) SEG GFR AX GO) as GF.
  refine (check_round_trip.check_round_trip_holds rc B (API rc) SEG MAL FRE ERR GF AX CO BSP _ _ _ _ CAL
            check_round_trip_stages_b.st8 fx).
  - rewrite TP. reflexivity.
  - unfold errno_addr. rewrite TP, EOFF. reflexivity.
  - rewrite GGD. reflexivity.
  - rewrite GRD. reflexivity.
Qed.

(* The reader's ubsan parse_items step (a Theorem Labs lane, lib/U/Prog/parse_items.v) and parse_value step (lib/U/Prog/parse_value.v)
   discharge the last two premises. *)
Lemma parse_items_step_cg_holds : CrtCallees.parse_items_step_ubsan.
Proof.
  intros B API LS SH SK empty FF rc d PV GR PS MS SKW FFR fx.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & FA).
  destruct (FA rc fx) as (_ & _ & _ & _ & _ & _ & CO & _ & _ & _ & _ & _ & _ & AX & _).
  exact (@parse_items.parse_items_step rc B (API rc) sb_form AX CO d PV GR PS MS FFR SKW fx).
Qed.

Lemma parse_value_step_cg_holds : CrtCallees.parse_value_step_ubsan.
Proof.
  intros B API LS SH SK empty FF rc d PI PS LIT SKW FM MC STD fx.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & FA).
  destruct (FA rc fx) as (_ & _ & _ & _ & _ & _ & CO & _ & _ & _ & EU & _ & _ & AX & _).
  exact (@parse_value.parse_value_step fx rc B (API rc) sb_form d AX CO EU (PI fx) (PS fx) LIT (FM fx) MC STD SKW).
Qed.

Theorem slot_premise_cg_proved : slot_premise_cg.
Proof.
  exact (LLVMFuzzerTestOneInput_cg_holds
           (slot_callees_cg_of (check_round_trip_cg_of parse_items_step_cg_holds parse_value_step_cg_holds))).
Qed.
