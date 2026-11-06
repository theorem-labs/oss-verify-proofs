(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from G_HARNESS_U of proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntry.v:52
   (origin/ossv/recipes 198234fa4d3) for libdiginet/fuzz_transport's ASan+UBSan image: the harness's own globals. *)
(* rule 24: proves no function (a constant: the harness globals' payload ranges of the ASan+UBSan image).

   G_HARNESS_B: the (start, length) ranges of fuzz_transport's writable harness globals in the ASan+UBSan image
   (fuzz_transport.asan-ubsan 41113a03c82f), the bytes a program call may change outside its own frame and the
   allocator's statics (libreac/fuzz_pcap's G form, lib/A/W_journalG.v ajournal_gx). Each range is one global's
   PAYLOAD (beg, size) as the image's own asan_globals descriptor states it (section asan_globals
   [0xa85a0, 0xa8fa0), 40 descriptors of 64 bytes: beg, size, size_with_redzone, name, module_name, ...); the
   redzone after each payload is not in G. All 18 are the .bss globals of fuzz/fuzz_transport.c, in address order;
   their hull is [0x5ded00, 0x5f2e10). The .data / .rodata descriptors (constants of the harness and the library)
   are not written by the program and are not in G. *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition G_HARNESS_B : list (Z * Z) := [
  (0x5ded00, 60);     (* g_cfg *)
  (0x5ded60, 4);      (* g_raw *)
  (0x5ded80, 8);      (* g_now *)
  (0x5deda0, 1);      (* g_fail_next *)
  (0x5dedc0, 4);      (* g_last_counter *)
  (0x5dede0, 1648);   (* M *)
  (0x5df5e0, 4);      (* g_nq *)
  (0x5df600, 4);      (* g_ncmd *)
  (0x5df620, 8);      (* g_rx *)
  (0x5df640, 18264);  (* g_s *)
  (0x5e4f60, 224);    (* GOT *)
  (0x5e5060, 4);      (* g_rx_send *)
  (0x5e5080, 40960);  (* g_cmd *)
  (0x5f1880, 4096);   (* g_q *)
  (0x5f2c80, 4);      (* g_rx_fail *)
  (0x5f2ca0, 4);      (* g_rx_times *)
  (0x5f2cc0, 8);      (* g_rx_len *)
  (0x5f2ce0, 304)     (* OW *)
].

(* The hull, for the start-up region cut and the driver's window (pcap's DRV_G_LO / DRV_G_HI, lib/A/AD1y.v:19-20). *)
Definition G_HARNESS_B_LO : Z := 0x5ded00.
Definition G_HARNESS_B_HI : Z := 0x5f2e10.

Lemma G_HARNESS_B_in_hull : forall r, In r G_HARNESS_B ->
  G_HARNESS_B_LO <= fst r /\ fst r + snd r <= G_HARNESS_B_HI.
Proof.
  intros r Hr. unfold G_HARNESS_B_LO, G_HARNESS_B_HI.
  repeat (destruct Hr as [<- | Hr]; [cbn; lia |]). destruct Hr.
Qed.
