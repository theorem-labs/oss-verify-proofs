(* lib/A/ProgWorldRtShadow.v -- shadow_rw_of_AR: ctrl's A.AsanRT.shadow_rw from the core's AR plus ProgWorld's
   AR_states_vis0_shadow, for A.ProgWorldRt (RT_used_of_AR's shadow_rw conjunct).  One writer (a Theorem Labs lane).
   ITERATION-ONLY; type-check evidence on the planning core only, never acceptance.  rule 24: no function proved.  This
   is a bridge lemma over the core's world (AR / aview / ahs), not a proof of any binary function.

   The proof is the shadow_rw branch of A.ProgWorldCtlRt.ctlrt_of_AR (ProgWorldCtlRt.v:546-573), which uses only AR
   and AR_states_vis0_shadow, restated under RT_used_of_AR's premises.  It reuses that file's helpers by name:
   aclient_byte_dec and exists_zr_dec (the case splits, no classical axiom), aclient_vis (a client byte is visible, from
   ARm's am_client) and mem_some_of_aview_high (above the image a visible byte is a byte of m).  A non-client byte is
   present by AR's ahs_pres (YG0n.v:442) when hidden or outside ly_vis0, and by AR_states_vis0_shadow (ProgWorld.v:94)
   when visible and in ly_vis0. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorld A.ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.AF0m A.AsanRT A.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.
(* The core's sink_head instance (A/AE2k.v:44), named explicitly since A.AE2k is only Required (as ProgWorld.v:76). *)
#[local] Existing Instance A.AE2k.tfib_sink_head.
Local Notation segs := A.AB1v.tfibsegs (only parsing).

Section RtShadow.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* Premises and binder order as A.ProgWorld.RT_used_of_AR_stmt (ProgWorld.v:879); CtrlTSyms and AR_laws are kept for
   that shape. *)
Lemma shadow_rw_of_AR :
  A.AF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B -> A.ProgWorld.AR_states_vis0_shadow B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> A.AsanRT.shadow_rw m.
Proof.
  intros _ _ Hvis0 ly S W m md HAR a Hsh.
  pose proof HAR as (HM & _ & _ & _ & HPres & _).
  assert (Hband : lib.Reusable.YG0f.in_band_rw a).
  { unfold lib.Reusable.YG0f.in_band_rw, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kLowShadowEnd,
      lib.Reusable.YG0f.kHighShadowBeg, lib.Reusable.YG0f.kHighShadowEnd.
    unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hsh.
    destruct Hsh as [[H1 H2]|[H1 H2]]; [left|right]; lia. }
  assert (Hhigh : 0x5fe000 <= a < 2 ^ 64).
  { unfold A.AsanRT.in_shadow, A.AsanRT.LOWMEM_END, A.AsanRT.LOWSHADOW_END, A.AsanRT.HIGHSHADOW_BEG,
      A.AsanRT.HIGHMEM_BEG in Hsh.
    change (2 ^ 64) with 18446744073709551616.
    destruct Hsh as [[H1 H2]|[H1 H2]]; lia. }
  assert (Hm : m (Z_to_bv 64 a) <> None).
  { destruct (A.ProgWorldCtlRt.aclient_byte_dec B ly S a) as [Hcl|Hcl].
    - apply (A.ProgWorldCtlRt.mem_some_of_aview_high W m a Hhigh).
      exact (A.ProgWorldCtlRt.aclient_vis B ly S _ a (lib.Reusable.YG0n.am_client _ _ _ _ HM) Hcl).
    - destruct (A.ProgWorldCtlRt.exists_zr_dec a (lib.Reusable.YG0f.ly_vis0 ly)) as [Hv|Hv].
      + destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EH.
        * exact (HPres a Hband Hcl (or_introl EH)).
        * exact (Hvis0 ly S W m md HAR a Hsh Hv EH).
      + exact (HPres a Hband Hcl (or_intror Hv)). }
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
  split.
  - unfold wview, Lib.Mem.wa. rewrite Em. discriminate.
  - exists b. unfold Lib.Mem.mrd, Lib.Mem.wa. rewrite Em. reflexivity.
Qed.

End RtShadow.

Print Assumptions shadow_rw_of_AR.
