(* fuzz_ctrl image A: the one step the cgif-form glue of ctrl_emit_as takes at a cut -- a lifted silent
   stretch of the footprint run, in the world.

   `ge_lift` is the spine: a configuration of the core's walk at pc `a` (YG0d.cfg_at) is the start state of a
   footprint run (A/ProgBridge.v cfg_at_MS, by conversion, up to the register map); the run's `evtF` becomes
   `fsteps` (ProgBridge.fevt_of_evtF), and Reusable/YA0nR.v `SRr_fevt_hid` walks the world along it at
   RNG := `ProgBridge.RNG_W (w_H W)`, whose footprint avoids the world's hidden memory by
   `ProgBridge.fp_avoids_RNG_W`. The continuation also gets the hidden bytes back unchanged, which is the form
   `YCbq.ajournal_exec` takes for the journal.

   The register map of a cut is the walk's own map; the run's start state names the registers one by one
   (lib/Lib/Regs6ss.v mkR). The two are `xregs_eqv`, and a walk does not tell them apart (YA0nR.SRr_xregs_eqv),
   so `ge_lift` takes that equivalence as its first premise and the caller produces it with
   Regs6ss.mkR_eqv_of from the call's `getr` facts.

   Glue closure rule (two Theorem Labs lanes, 2026-10-28 23:38Z): no _F file is Imported here; this file names
   none of them at all. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import GEbase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Regs6ss.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
#[local] Notation SEGS := AB1v.tfibsegs.

Lemma ge_lift : forall (W : world SEGS) (a : Z) (regs R : bvmap 5 word) (memc : word -> option byte)
    (mdc : Model) (P : machine_state -> Prop) (Q : world SEGS -> config -> Prop),
  wx_segs_nowrap SEGS ->
  xregs_eqv R regs ->
  ExecF.evtF rsegs (RNG_W (w_H W)) P (MS R lib.Reusable.YK11.fp_regs (Z_to_bv 64 a) lib.Reusable.YK11.fp_csr None memc (seg_rom SEGS)) ->
  (forall (ms' : machine_state) (mdc' : Model), P ms' ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = memc x) ->
     same_but_materialized mdc mdc' -> SRr SEGS W (mkCfg ms' mdc') Q) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc) Q.
Proof.
  intros W a regs R memc mdc P Q Hwx HR HE K.
  rewrite (cfg_at_MS SEGS a regs memc mdc).
  apply (SRr_xregs_eqv SEGS W R regs lib.Reusable.YK11.fp_regs (Z_to_bv 64 a) lib.Reusable.YK11.fp_csr None memc (seg_rom SEGS) mdc Q);
    [| exact HR].
  apply (SRr_fevt_hid SEGS Hwx W _ mdc (RNG_W (w_H W)) P Q).
  - exact (fevt_of_evtF (RNG_W (w_H W)) P _ HE).
  - exact (fp_avoids_RNG_W (w_H W)).
  - intros ms' mdc' HP Hhid Hsame. exact (K ms' mdc' HP Hhid Hsame).
Qed.

End b.
