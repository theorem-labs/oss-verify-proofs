(* The walks put together: check_round_trip (check_round_trip.v) for every allocator of the slot, with the
   addresses of malloc and free and AllocExtra from llvm_binds, ctx_owned and the malloc and free contracts from
   llvm_frame's frame_allocator, the errno bound, the kit's memset, memcpy and bcmp (memset.v, memcpy.v, bcmp.v),
   and diginet_frame_build by its contract; then LLVMFuzzerTestOneInput_link.v with the walks of
   diginet_frame_parse, check_parse_refusal, check_parse_fields, check_announce and their callees.
   frame_build_of_walks gives diginet_frame_build's contract from its walk, whose premises are the contracts of
   diginet_body_check, memcpy and memset; slot_sr_all_holds and plain_halts_holds put in the walk of
   diginet_frame_build (diginet_frame_build.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import memcpy_c memset_c bcmp_c memcpy memset bcmp
  diginet_frame_build_c diginet_body_check_c diginet_cursor_init_c diginet_msg_next_c
  diginet_body_check diginet_cursor_init diginet_msg_next
  diginet_frame_parse_c diginet_frame_parse check_parse_refusal_c check_parse_refusal
  diginet_mac_is_digidesign_c diginet_mac_is_digidesign diginet_frame_is_keepalive_c diginet_frame_is_keepalive
  check_parse_fields_c check_parse_fields diginet_announce_parse_c diginet_announce_parse
  check_announce_c check_announce check_round_trip_c check_round_trip
  LLVMFuzzerTestOneInput_c Statement LLVMFuzzerTestOneInput_link.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require diginet_frame_build.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* LLVMFuzzerTestOneInput_link.v check_round_trip_all from the walk of check_round_trip. *)
Theorem check_round_trip_all_of_build : diginet_frame_build_contract -> check_round_trip_all.
Proof.
  intros BUILD rc fx B API HA Hel BI.
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
  - exact memcpy_holds.
  - exact bcmp_holds.
  - exact BUILD.
Qed.

(* Statement.v slot_sr_all, the plain premise of LLVMFuzzerTestOneInput_agree.v ubsan_agrees_of_llvm. *)
Theorem slot_sr_all_of_build : diginet_frame_build_contract -> slot_sr_all.
Proof.
  intros BUILD.
  exact (slot_sr_all_of_callees memcpy_holds memset_holds (diginet_frame_parse_holds memcpy_holds)
    check_parse_refusal_holds
    (check_parse_fields_holds bcmp_holds diginet_mac_is_digidesign_holds diginet_frame_is_keepalive_holds)
    (check_round_trip_all_of_build BUILD)
    (check_announce_holds memset_holds diginet_announce_parse_holds bcmp_holds)).
Qed.

Theorem plain_halts_of_build : diginet_frame_build_contract -> Statements.plain_halts.
Proof.
  intros BUILD.
  exact (plain_halts_holds_of_walks memcpy_holds memset_holds (diginet_frame_parse_holds memcpy_holds)
    check_parse_refusal_holds
    (check_parse_fields_holds bcmp_holds diginet_mac_is_digidesign_holds diginet_frame_is_keepalive_holds)
    (check_round_trip_all_of_build BUILD)
    (check_announce_holds memset_holds diginet_announce_parse_holds bcmp_holds)).
Qed.

(* diginet_frame_build's contract from its walk, with the walks of its callees. *)
Theorem frame_build_of_walks :
  (diginet_body_check_contract -> memcpy_contract -> memset_contract -> diginet_frame_build_contract) ->
  diginet_frame_build_contract.
Proof.
  intros W.
  exact (W (diginet_body_check_holds diginet_cursor_init_holds diginet_msg_next_holds) memcpy_holds memset_holds).
Qed.

Theorem slot_sr_all_holds : slot_sr_all.
Proof. exact (slot_sr_all_of_build (frame_build_of_walks diginet_frame_build.diginet_frame_build_holds)). Qed.

Theorem plain_halts_holds : Statements.plain_halts.
Proof. exact (plain_halts_of_build (frame_build_of_walks diginet_frame_build.diginet_frame_build_holds)). Qed.
