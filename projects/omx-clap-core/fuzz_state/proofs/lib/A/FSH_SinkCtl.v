(* POSITIVE CONTROL for the sink guard (owner a Theorem Labs lane 03:47Z; method a Theorem Labs lane 02:29Z, a Theorem Labs lane 03:00Z).
   The guard in the statement and kit files is a `Fail Definition ... := _.` per sink class. A `Fail` line
   that holds proves nothing on its own: it also holds when the CLASS NAME is wrong, when the class is not
   loaded, or when nothing could ever resolve. This file is the other half of the measurement: with the
   image's own instances imported, the SAME placeholders DO resolve, so a `Fail` elsewhere means "no instance
   in scope", not "the probe is dead".
   `probe_pos_SK` resolves to AE2k's tfib_sink_head (fs.asan's own ofl_head); `probe_pos_SH` resolves to
   YI5c.src0_sink, the plain line's instance, which is the only sink_syms instance in the tree.
   NOT PART OF THE COUNTED TARGET SET: this file proves no function and no statement of fs depends on it
   (rule 24: no function proved; kind: statement text / control). It is built by hand when the guard changes.
   If either line below ever fails to compile, the guard has gone dead and the `Fail` lines mean nothing.
   GUARD EXCEPTIONS (files with no `Fail` guard line): lib/A/FSTfibParts.v. MEASURED (a Theorem Labs lane 06:45Z, build
   log build-20261029T064547Z), not assumed: in that file BOTH bare placeholders RESOLVE - probe_SH prints
   `YI5c.src0_sink`, the plain line's instance, and the probe_SK `Fail` reports "The command has not failed!".
   So it can carry no `Fail` line, and the static claim that its closure lacks YI5c (a Theorem Labs lane 06:28Z) is false:
   YI5c arrives transitively. Its own text names no sink_syms and passes sink_head explicitly through AE2k. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YI14 YI5c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AE2k.

Definition probe_pos_SK : Reusable.YI16.sink_head := _.
Definition probe_pos_SH : Reusable.YI14.sink_syms := _.
