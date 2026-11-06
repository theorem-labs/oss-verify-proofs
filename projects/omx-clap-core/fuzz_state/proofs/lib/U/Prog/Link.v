From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YM05 YO0f YO0d YO09 YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import StatementHalts LLVMFuzzerTestOneInput
  memchr_c memcpy_c memset_c strlen_c bcmp_c fuzz_alloc_live_c fuzz_alloc_peak_c fuzz_alloc_peak_reset_c
  fuzz_alloc_fail_c check_bounded_alloc_c check_reject_clean_c check_no_overread_c check_as_written_c
  check_round_trip_c check_reject_clean_starved_c past_nul_c fuzz_malloc_c fuzz_free_c preset_base64_decode_c
  preset_base64_encode_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import memchr memcpy memset strlen bcmp
  fuzz_alloc_live fuzz_alloc_peak fuzz_alloc_peak_reset fuzz_alloc_fail check_bounded_alloc check_reject_clean
  check_no_overread check_as_written check_reject_clean_starved past_nul fuzz_malloc fuzz_free preset_base64_decode
  preset_base64_encode.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require FrameProof.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require check_round_trip check_round_trip_stages_b CrtCallees strtod_c parse_items parse_value.
From OSSVerify.omx_clap_core.fuzz_state Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* The ubsan build's statement from the frame's statement: the callee contracts of entry_fn are the proved X_holds
   theorems, their premises taken from frame_facts_ubsan (frame_allocator for the allocator facts). check_round_trip
   is the one callee whose contract is not proved here: it stays the premise check_round_trip_ubsan. *)

(* Needed by slot_callees_ubsan_of for check_round_trip_contract, which no theorem proves yet. *)
Definition check_round_trip_ubsan : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_ubsan B API LS SH SK empty ->
    forall (rc : RunCeil) (fx : FPState), check_round_trip_contract B (API rc).

Ltac link_disch :=
  first [ assumption | exact memchr_holds | exact memcpy_holds | exact memset_holds | exact strlen_holds
        | exact bcmp_holds | exact fuzz_alloc_live_holds | exact fuzz_alloc_fail_holds ].

Theorem slot_callees_ubsan_of : check_round_trip_ubsan -> slot_callees_ubsan.
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

Theorem ubsan_halts_link : frame_ubsan -> check_round_trip_ubsan -> Statements.ubsan_halts.
Proof.
  intros FR CRT.
  apply (ubsan_halts_of_frame FR), LLVMFuzzerTestOneInput_holds, slot_callees_ubsan_of, CRT.
Qed.

Print Assumptions ubsan_halts_link.

(* The frame's own statement is proved (FrameProof.v); check_round_trip's contract is the one open premise. *)
Theorem ubsan_halts_closed : check_round_trip_ubsan -> Statements.ubsan_halts.
Proof. exact (ubsan_halts_link FrameProof.frame_ubsan_holds). Qed.

(* check_round_trip's contract from its proof, the callee contracts (CrtCallees) and the frame facts. The one premise
   left is the reader's parse_items step (CrtCallees.parse_items_step_ubsan). *)
Theorem check_round_trip_ubsan_of : CrtCallees.parse_items_step_ubsan -> CrtCallees.parse_value_step_ubsan -> check_round_trip_ubsan.
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

Theorem ubsan_halts_final : CrtCallees.parse_items_step_ubsan -> CrtCallees.parse_value_step_ubsan -> Statements.ubsan_halts.
Proof. intros PI PV. exact (ubsan_halts_closed (check_round_trip_ubsan_of PI PV)). Qed.

(* The reader's ubsan parse_items step (a Theorem Labs lane, lib/U/Prog/parse_items.v) and parse_value step (lib/U/Prog/parse_value.v)
   discharge the last two premises. *)
Lemma parse_items_step_ubsan_holds : CrtCallees.parse_items_step_ubsan.
Proof.
  intros B API LS SH SK empty FF rc d PV GR PS MS SKW FFR fx.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & FA).
  destruct (FA rc fx) as (_ & _ & _ & _ & _ & _ & CO & _ & _ & _ & _ & _ & _ & AX & _).
  exact (@parse_items.parse_items_step rc B (API rc) sb_form AX CO d PV GR PS MS FFR SKW fx).
Qed.

Lemma parse_value_step_ubsan_holds : CrtCallees.parse_value_step_ubsan.
Proof.
  intros B API LS SH SK empty FF rc d PI PS LIT SKW FM MC STD fx.
  destruct FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & FA).
  destruct (FA rc fx) as (_ & _ & _ & _ & _ & _ & CO & _ & _ & _ & EU & _ & _ & AX & _).
  exact (@parse_value.parse_value_step fx rc B (API rc) sb_form d AX CO EU (PI fx) (PS fx) LIT (FM fx) MC STD SKW).
Qed.

Theorem ubsan_halts_proved : Statements.ubsan_halts.
Proof. exact (ubsan_halts_final parse_items_step_ubsan_holds parse_value_step_ubsan_holds). Qed.

Print Assumptions ubsan_halts_proved.
