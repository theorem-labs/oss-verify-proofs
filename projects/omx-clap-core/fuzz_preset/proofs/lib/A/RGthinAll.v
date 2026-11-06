(* Modified by Theorem Labs, 2026-10-29: relocated from proofs/plugin-hostd/fuzz_reply/lib/A/RGthinAll.v (hub 66a127cb11e, blob 02590e8acb46) to omx-clap-core/fuzz_preset's asan image A by a Theorem Labs lane's internal file alreloc.py (frozen-c4338d099cfb8025); record, the internal file A5.md. *)
(* fuzz_preset.asan image A: the five thin realloc segments of RGtop together, with their axiom report. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import RGthinK RGthinM RGthinM2 RGthinS RGthinS2a RGthinS2b RGthinS3 RGthinS4 RGthinS6.
Print Assumptions rt_seg_mid_a.
Print Assumptions rt_seg_mid_b.
Print Assumptions rt_seg_ret.
Print Assumptions rt_seg_nret.
Print Assumptions rt_seg_npost.
