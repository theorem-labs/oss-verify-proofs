(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X00a.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fg X0fy X001 X07z X05s X081 X05m X06d X069
X068 X05a X08y X08u X08p X0b0 X0b6 X084 X0bi X0ao X067
X0c3 X0c5 X0c4 X0ei X0bu X0eh X047 X0jd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma IO_sspA : forall y, in_ranges IO_FPA y -> ~ (X00a.SSP_GUARD <= y < X00a.SSP_GUARD + 8).
Proof.
intros y (lo & hi & Hin & Hy). unfold IO_FPA in Hin. unfold X00a.SSP_GUARD. cbn [In] in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Definition AFA : art_facts RTA := rc_facts RTA rta_contracts_closed.
Definition AF_DRVA : forall Σ m, ART RTA Σ m -> drv_consts m := rta_drv AFA rta_io.
Definition IO_imgA1 : forall y, in_ranges IO_FPA y -> client_static y := fun y H => proj1 (IO_imgA y H).
Definition IO_drvA : forall y, in_ranges IO_FPA y -> ~ drv_cell y := fun y H => proj1 (proj2 (IO_imgA y H)).

Section Closure.
Hypothesis EH : @nbd_EH_cps RTA bptr.

Theorem dec_cps_allA : forall d : dec_state bptr,
dec_cps_at RTA OUT_repA ERR_repA IO_FPA A_speex_decode_native d /\ dec_cps_at RTA OUT_repA ERR_repA IO_FPA A_speex_decode d.
Proof using EH.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (dec_cps_all RTA AFA OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgA1 IO_sspA AF_DRVA rta_acc_stderr_var rta_lib_consts rta_fprintf_lib
(rc_stack_malloc_0 RTA RC) (rx_alloca_poison RTA RX) rta_allocas_unpoison_lo (rx_allocas_unpoison_nop RTA RX) (rc_asan_memset RTA RC)
(qmf_synth16_ok RTA AFA (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX))
(sbl_subframe RTA AFA rta_lib_consts (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_allocas_unpoison_lo (rc_asan_memset RTA RC)
(lsp_to_lpc8_ok RTA AFA (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) (rc_asan_memset RTA RC))
(@split_cb_innov RTA bptr AFA (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_lib_consts))
(nb_decode_cps RTA AFA OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgA1 AF_DRVA rta_acc_stderr_var rta_lib_consts rta_fprintf_lib
(rx_stack_malloc_5 RTA RX) (rx_stack_free RTA RX 5%nat (or_introl eq_refl)) (rx_asan_memmove RTA RX) (rc_asan_memcpy RTA RC) (rc_asan_memset RTA RC) EH)).
Qed.
End Closure.
