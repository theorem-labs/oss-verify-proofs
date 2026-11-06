(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Print Assumptions probe for lib/B/FSRawLeafWitness.v (the route-1 raw-frame leaf witnesses at image B's real
   instance), so the full-unit build log carries each witness's axiom list, named. *)
(* Modified by Theorem Labs, 2026-10: new file; assumptions probe for the image-B leaf witnesses. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSRawLeafWitness.
Print Assumptions FSRawLeafWitness.w_refill.
Print Assumptions FSRawLeafWitness.w_cdealloc.
Print Assumptions FSRawLeafWitness.w_rchunk.
Print Assumptions FSRawLeafWitness.w_dorecycle.
Print Assumptions FSRawLeafWitness.w_drain.
Print Assumptions FSRawLeafWitness.w_enqueue_room.
Print Assumptions FSRawLeafWitness.w_enqueue_nb.
