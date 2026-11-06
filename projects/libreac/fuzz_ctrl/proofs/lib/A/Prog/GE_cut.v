(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 26 of its 38 lines of code are new or changed and 999 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/GE_entry.v; 32 of its 53 lines of code are new or changed and 17 lines of the source are left out. *)
(* fuzz_ctrl image A: the three moves the cgif-form glue of ctrl_emit_as makes at its one cut, the
   ctrl_lay_block call at 0x84cec.

   `ge_cases`  : the first lifted stretch ends at one of two states (ctrl_emit_asF2.aMid is `aQp \/ aAtLay`:
                 the early return of the EE = false regime, or the call site), and the walk continues from
                 whichever it is.
   `ge_steps`  : a footprint run with no event -- here the single `jal` of the call -- moves the walk from one
                 machine state to the next (YA0nR.SRr_fsteps at RNG := ProgBridge.RNG_W (w_H W)).
   `ge_at_cfg` : a machine state written as a run writes it IS the walk's configuration at that pc
                 (A/ProgBridge.v cfg_at_MS), which is the form a caller-journal contract -- here
                 C_ctrl_lay_block.v's tctrl_lay_block_spec -- is stated in.

   With them the glue is: ge_entry (GE_entry.v) with the first stretch, ge_cases, then on the call-site arm
   ge_steps with the `jal` and ge_at_cfg, which hands the state to the callee's contract; its post feeds the
   second stretch through ge_lift again. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase GE_lift GE_entry.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

(* A lifted stretch whose post is a disjunction: one continuation per arm. *)
Lemma ge_cases : forall (W : world SEGS) (a : Z) (regs : bvmap 5 word) (memc : word -> option byte)
    (mdc : Model) (P1 P2 : machine_state -> Prop) (Q : world SEGS -> config -> Prop),
  wx_segs_nowrap SEGS ->
  ExecF.evtF rsegs (RNG_W (w_H W)) (fun ms => P1 ms \/ P2 ms)
    (MS (mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
             (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13)
             (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
             (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
             (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31))
        lib.Reusable.YK11.fp_regs (Z_to_bv 64 a) lib.Reusable.YK11.fp_csr None memc (seg_rom SEGS)) ->
  (forall (ms' : machine_state) (mdc' : Model), P1 ms' ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = memc x) ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  (forall (ms' : machine_state) (mdc' : Model), P2 ms' ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = memc x) ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc) Q.
Proof.
  intros W a regs memc mdc P1 P2 Q Hwx HE K1 K2.
  apply (ge_entry W a regs memc mdc (fun ms => P1 ms \/ P2 ms) Q Hwx HE).
  intros ms' mdc' [H1 | H2] Hhid Hsame; [exact (K1 ms' mdc' H1 Hhid Hsame) | exact (K2 ms' mdc' H2 Hhid Hsame)].
Qed.

(* A footprint run with no event moves the walk along it. *)
Lemma ge_steps : forall (W : world SEGS) (ms ms' : machine_state) (md : Model) (Q : world SEGS -> config -> Prop),
  wx_segs_nowrap SEGS ->
  ExecF.mstepsF rsegs (RNG_W (w_H W)) ms ms' ->
  (forall md' : Model, same_but_materialized md md' -> SRr SEGS W (mkCfg ms' md') Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
  intros W ms ms' md Q Hwx Hrun K.
  apply (SRr_fsteps SEGS Hwx W ms ms' md (RNG_W (w_H W)) Q).
  - exact (fsteps_of_mstepsF (RNG_W (w_H W)) ms ms' Hrun).
  - exact (fp_avoids_RNG_W (w_H W)).
  - exact K.
Qed.

(* The run's state at a pc IS the walk's configuration there, so a caller-journal contract applies to it. *)
Lemma ge_at_cfg : forall (W : world SEGS) (R : bvmap 5 word) (pc : Z) (mc : word -> option byte) (md : Model)
    (Q : world SEGS -> config -> Prop),
  SRr SEGS W (cfg_at SEGS pc R mc md) Q ->
  SRr SEGS W (mkCfg (MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mc (seg_rom SEGS)) md) Q.
Proof. intros W R pc mc md Q H. rewrite (cfg_at_MS SEGS pc R mc md) in H. exact H. Qed.

(* and back, for a state the walk hands to a lifted stretch *)
Lemma ge_of_cfg : forall (W : world SEGS) (R : bvmap 5 word) (pc : Z) (mc : word -> option byte) (md : Model)
    (Q : world SEGS -> config -> Prop),
  SRr SEGS W (mkCfg (MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 pc) lib.Reusable.YK11.fp_csr None mc (seg_rom SEGS)) md) Q ->
  SRr SEGS W (cfg_at SEGS pc R mc md) Q.
Proof. intros W R pc mc md Q H. rewrite (cfg_at_MS SEGS pc R mc md). exact H. Qed.

End b.
