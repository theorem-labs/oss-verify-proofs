(* The walks put together: check_round_trip (U/Prog/check_round_trip.v) and its crash-free walk
   (U/Prog/check_round_trip_cg.v) for every allocator of the slot, with the addresses of malloc and free and
   AllocExtra from llvm_binds, ctx_owned, the malloc and free contracts and the errno bound from llvm_frame (for the
   crash-free walk, the crash-free malloc through malloc_ag_of_cf with llvm_limlaw), the kit's memset and bcmp
   (U/Prog/memset.v, bcmp.v), the walk of spec_build_frame (U/Prog/spec_build_frame.v) and diginet_frame_build by its
   contract; then U/Prog/LLVMFuzzerTestOneInput_link.v with the walks of diginet_frame_parse, check_parse_refusal,
   check_parse_fields, check_announce and their callees. frame_build_of_walks gives diginet_frame_build's contract
   from its walk, whose premises are the contracts of diginet_body_check, memcpy, diginet_sum16 and memset;
   ubsan_halts_holds puts in the walk of diginet_frame_build (U/Prog/diginet_frame_build.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0 FrameAPI SlotAgree AgreeLift.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import memcpy_c memset_c bcmp_c memcpy memset bcmp
  rd32_c rd32 diginet_sum16_c diginet_sum16 copy_strz_c copy_strz
  diginet_frame_build_c diginet_body_check_c diginet_cursor_init_c diginet_msg_next_c
  diginet_body_check diginet_cursor_init diginet_msg_next spec_build_frame_c spec_build_frame
  diginet_frame_parse_c diginet_frame_parse check_parse_refusal_c check_parse_refusal
  diginet_mac_is_digidesign_c diginet_mac_is_digidesign diginet_frame_is_keepalive_c diginet_frame_is_keepalive
  check_parse_fields_c check_parse_fields diginet_announce_parse_c diginet_announce_parse
  check_announce_c check_announce check_round_trip_c check_round_trip check_round_trip_ccf check_round_trip_cg
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_cfb Statement LLVMFuzzerTestOneInput_link.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require diginet_frame_build.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* The hypothesis CRT of U/Prog/LLVMFuzzerTestOneInput_link.v from the walk of check_round_trip. *)
Theorem crt_of_build : diginet_frame_build_contract ->
  forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK -> llvm_binds B API -> @check_round_trip_contract fx rc B API.
Proof.
  intros BUILD rc fx B API SH SK FR BI.
  destruct FR as (HA & Hel & _).
  destruct BI as (_ & Hm & Hf & _ & _ & HX).
  destruct (HA fx) as (_ & _ & _ & _ & _ & _ & CT & _).
  apply check_round_trip_holds.
  - exact Hm.
  - exact Hf.
  - exact Hel.
  - exact HX.
  - exact CT.
  - intros fx'. exact (proj1 (HA fx')).
  - intros fx'. exact (proj1 (proj2 (HA fx'))).
  - exact memset_holds.
  - exact bcmp_holds.
  - exact BUILD.
  - exact (spec_build_frame_holds memset_holds memcpy_holds).
Qed.

(* The hypothesis CRT_CF of U/Prog/LLVMFuzzerTestOneInput_link.v from the crash-free walk of check_round_trip. *)
Theorem crt_cf_of_build : diginet_frame_build_contract ->
  forall (rc : RunCeil) (fx : FPState) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK -> llvm_binds B API ->
    (forall fx' : FPState, @malloc_contract_cf fx' rc B API) ->
    (forall fx' : FPState, @free_contract_cf fx' rc B API) ->
    llvm_limlaw B API ->
    @check_round_trip_contract_cf fx rc B API.
Proof.
  intros BUILD rc fx B API SH SK FR BI MCF FCF LIM.
  destruct FR as (HA & Hel & _).
  destruct BI as (_ & Hm & Hf & _ & _ & HX).
  destruct (HA fx) as (_ & _ & _ & _ & _ & _ & CT & _).
  apply check_round_trip_holds_cf.
  - exact Hm.
  - exact Hf.
  - exact Hel.
  - exact HX.
  - exact CT.
  - intros fx'. exact (malloc_ag_of_cf B API LIM (MCF fx')).
  - intros fx'. exact (FCF fx').
  - exact memset_holds.
  - exact bcmp_holds.
  - exact BUILD.
  - exact (spec_build_frame_holds memset_holds memcpy_holds).
Qed.

Lemma parse_walk : diginet_frame_parse_contract.
Proof. exact (diginet_frame_parse_holds memcpy_holds rd32_holds diginet_sum16_holds). Qed.

Lemma fields_walk : check_parse_fields_contract.
Proof.
  exact (check_parse_fields_holds bcmp_holds diginet_mac_is_digidesign_holds diginet_frame_is_keepalive_holds).
Qed.

Lemma announce_walk : check_announce_contract.
Proof. exact (check_announce_holds memset_holds (diginet_announce_parse_holds copy_strz_holds) bcmp_holds). Qed.

(* U/Prog/Statement.v slot_sr_cf_all, the UBSan premise of Prog/LLVMFuzzerTestOneInput_agree.v
   ubsan_agrees_of_llvm. *)
Theorem slot_sr_cf_all_of_build : diginet_frame_build_contract -> slot_sr_cf_all.
Proof.
  intros BUILD.
  pose proof parse_walk as PARSE. pose proof check_parse_refusal_holds as CPR.
  pose proof fields_walk as CPF. pose proof announce_walk as CA.
  pose proof (crt_cf_of_build BUILD) as CRT_CF.
  eapply slot_sr_cf_holds; eassumption.
Qed.

Theorem ubsan_halts_of_build : diginet_frame_build_contract -> Statements.ubsan_halts.
Proof.
  intros BUILD.
  pose proof parse_walk as PARSE. pose proof check_parse_refusal_holds as CPR.
  pose proof fields_walk as CPF. pose proof announce_walk as CA.
  pose proof (crt_of_build BUILD) as CRT.
  eapply ubsan_halts_holds_of_walks; eassumption.
Qed.

(* diginet_frame_build's UBSan contract from its walk, with the walks of its callees. *)
Theorem frame_build_of_walks :
  (diginet_body_check_contract -> memcpy_contract -> diginet_sum16_contract -> memset_contract ->
   diginet_frame_build_contract) ->
  diginet_frame_build_contract.
Proof.
  intros W.
  exact (W (diginet_body_check_holds diginet_cursor_init_holds diginet_msg_next_holds) memcpy_holds
    diginet_sum16_holds memset_holds).
Qed.

Theorem ubsan_halts_holds : Statements.ubsan_halts.
Proof. exact (ubsan_halts_of_build (frame_build_of_walks diginet_frame_build.diginet_frame_build_holds)). Qed.
