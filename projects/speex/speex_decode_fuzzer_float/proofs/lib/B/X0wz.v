(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05m X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X161 X16j X0r0 X0yr X0wl X0ys X0x2
X0x1 X0w7 X0zq X0zl X0zg X11k X122 X11i X119 X0x0
X12o X12q X12p X153 X12f X152 X0v5 X19u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma IO_sspB : forall y, in_ranges IO_FPA y -> ~ (B.X0r9.SSP_GUARD <= y < B.X0r9.SSP_GUARD + 8).
Proof.
intros y (lo & hi & Hin & Hy). unfold IO_FPA in Hin. unfold B.X0r9.SSP_GUARD. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Definition AFB : art_facts RTA := rc_facts RTA rta_contracts_closed.
Definition AF_DRVB : forall Σ m, ART RTA Σ m -> drv_consts m := rta_drv AFB rta_io.
Definition IO_imgB1 : forall y, in_ranges IO_FPA y -> client_static y := fun y H => proj1 (IO_imgA y H).
Definition IO_drvB : forall y, in_ranges IO_FPA y -> ~ drv_cell y := fun y H => proj1 (proj2 (IO_imgA y H)).

Section Closure.
Hypothesis EH : @nbd_EH_cps RTA bptr.
Hypothesis LOOP : sb_subframe_cps RTA.

Theorem dec_cps_allB : forall d : dec_state bptr,
dec_cps_at RTA OUT_repA ERR_repA IO_FPA A_speex_decode_native d /\ dec_cps_at RTA OUT_repA ERR_repA IO_FPA A_speex_decode d.
Proof using EH LOOP.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (dec_cps_all RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 IO_sspB AF_DRVB rta_acc_stderr_var rta_lib_consts rta_fprintf_lib
(rc_stack_malloc_0 RTA RC) (rx_alloca_poison RTA RX) rta_allocas_unpoison_lo (rx_allocas_unpoison_nop RTA RX) (rc_asan_memset RTA RC)
(qmf_synth16_ok RTA AFB (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX))
LOOP
(nb_decode_cps RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 AF_DRVB rta_acc_stderr_var rta_lib_consts rta_fprintf_lib
(rx_stack_malloc_5 RTA RX) (rx_stack_free RTA RX 5%nat (or_introl eq_refl)) (rx_asan_memmove RTA RX) (rc_asan_memset RTA RC) EH)).
Qed.
End Closure.
