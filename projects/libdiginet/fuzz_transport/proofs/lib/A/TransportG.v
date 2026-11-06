(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from G_HARNESS_U of proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntry.v:52
   (origin/ossv/recipes 198234fa4d3) for libdiginet/fuzz_transport's ASan+UBSan image: the harness's own globals. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/TransportGB.v, with its addresses changed; 6 of its 31 lines of code are new or changed and 7 lines of the source are left out. *)
(* G_HARNESS: the (start, length) ranges of fuzz_transport's writable harness globals in the ASan image
   (fuzz_transport.asan e89be137db17), the bytes a program call may change outside its own frame and the allocator's
   statics (the G form of lib/A/W_journalG.v, ajournal_gx). Each range is one global's PAYLOAD (beg, size) as the
   image's own asan_globals descriptor states it (section asan_globals [0xa8940, 0xa9340), 40 descriptors of 64 bytes:
   beg, size, size_with_redzone, ...); the redzone after each payload is not in G. All 18 are the .bss globals of
   fuzz/fuzz_transport.c, in address order; their hull is [0x5df080, 0x5f3190). The .data / .rodata descriptors
   (constants of the harness and the library) are not written by the program and are not in G. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition G_HARNESS : list (Z * Z) := [
  (0x5df080, 60);     (* g_cfg *)
  (0x5df0e0, 4);      (* g_raw *)
  (0x5df100, 8);      (* g_now *)
  (0x5df120, 1);      (* g_fail_next *)
  (0x5df140, 4);      (* g_last_counter *)
  (0x5df160, 1648);   (* M *)
  (0x5df960, 4);      (* g_nq *)
  (0x5df980, 4);      (* g_ncmd *)
  (0x5df9a0, 8);      (* g_rx *)
  (0x5df9c0, 18264);  (* g_s *)
  (0x5e52e0, 224);    (* GOT *)
  (0x5e53e0, 4);      (* g_rx_send *)
  (0x5e5400, 40960);  (* g_cmd *)
  (0x5f1c00, 4096);   (* g_q *)
  (0x5f3000, 4);      (* g_rx_fail *)
  (0x5f3020, 4);      (* g_rx_times *)
  (0x5f3040, 8);      (* g_rx_len *)
  (0x5f3060, 304)     (* OW *)
].

(* The hull, for the start-up region cut and the driver's window. *)
Definition G_HARNESS_LO : Z := 0x5df080.
Definition G_HARNESS_HI : Z := 0x5f3190.

Lemma G_HARNESS_in_hull : forall r, In r G_HARNESS ->
  G_HARNESS_LO <= fst r /\ fst r + snd r <= G_HARNESS_HI.
Proof.
  intros r Hr. unfold G_HARNESS_LO, G_HARNESS_HI.
  repeat (destruct Hr as [<- | Hr]; [cbn; lia |]). destruct Hr.
Qed.
