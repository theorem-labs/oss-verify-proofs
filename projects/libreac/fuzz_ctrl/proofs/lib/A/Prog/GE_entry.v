(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 26 of its 38 lines of code are new or changed and 999 lines of the source are left out. *)
(* fuzz_ctrl image A: the glue's entry conversion -- a cut of the core's walk, written with the walk's own
   register map, as the start state of a footprint run, which names the 31 registers one by one.

   `ge_entry` is `GE_lift.ge_lift` with the register side discharged: the canonical map of a footprint run is
   `Regs6ss.mkR (getr regs 1) .. (getr regs 31)`, which is `Regs6ss.mkR_of regs` up to `getr r = reg_get r`
   for r <> 0 (lib.Reusable.YK11.v:23), and a walk does not tell the two apart (YA0nR.SRr_xregs_eqv). A caller then rewrites
   each `getr regs i` with the call's own premise (`getr regs 10 = w64 p` and so on). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase GE_lift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* The walk's map written register by register. *)
Lemma ge_mkR_of : forall regs : bvmap 5 word,
  mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma ge_entry : forall (W : world SEGS) (a : Z) (regs : bvmap 5 word) (memc : word -> option byte)
    (mdc : Model) (P : machine_state -> Prop) (Q : world SEGS -> config -> Prop),
  wx_segs_nowrap SEGS ->
  ExecF.evtF rsegs (RNG_W (w_H W)) P
    (MS (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
             (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
             (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
             (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
             (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31))
        lib.Reusable.YK11.fp_regs (Z_to_bv 64 a) lib.Reusable.YK11.fp_csr None memc (seg_rom SEGS)) ->
  (forall (ms' : machine_state) (mdc' : Model), P ms' ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = memc x) ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc) Q.
Proof.
  intros W a regs memc mdc P Q Hwx HE K.
  apply (ge_lift W a regs (mkR_of regs) memc mdc P Q Hwx).
  - exact (xregs_eqv_sym regs (mkR_of regs) (mkR_of_eqv regs)).
  - rewrite ge_mkR_of. exact HE.
  - exact K.
Qed.

End b.
