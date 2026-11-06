(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldRtShadow.v (a working branch 4fc53b7121d, blob caea6124a48; re-synced to a48c4068c6e (an earlier version, blob 557a3aca029, not in this delivery), the same blob at 1d23ced37fd: A's YK11 YM05 YA0n Require now names lib.Reusable, and B takes it): the same lemma shadow_rw_of_AR and the same proof over image B (asan-ubsan).  Differences from A: module paths (A.ProgWorld / ProgWorldCtlRt / AsanRT / Img0 -> B.*; A.AB1v / AE2k / AF0m -> lib.Reusable.YB1v / YE2k / YF0m); every other Require as A writes it, except Lib.Mem, which also exists as lib/B/Bz/Lib/Mem.v: Required as `From ...fuzz_ctrl.lib.Lib Require Mem` and named lib.Lib.Mem (fix_require6.py, as lib/B/ProgWorld.v on the base; A: `Require Lib.Mem`, Lib.Mem); the image hull end is written by name, B.Prog.ImgBounds.IMG_HI (= 0x5fe000, the bound of B.ProgWorldCtlRt.mem_some_of_aview_high), where A writes the literal (one extra Require, and one extra proof step that unfolds IMG_HI). *)
(* lib/B/ProgWorldRtShadow.v -- shadow_rw_of_AR: ctrl's B.AsanRT.shadow_rw from the core's AR plus ProgWorld's
   AR_states_vis0_shadow, for B.ProgWorldRt (RT_used_of_AR's shadow_rw conjunct).  rule 24: no function proved.  This
   is a bridge lemma over the core's world (AR / aview / ahs), not a proof of any binary function.

   The proof is the shadow_rw branch of B.ProgWorldCtlRt.ctlrt_of_AR, which uses only AR and AR_states_vis0_shadow,
   restated under RT_used_of_AR's premises.  It reuses that file's helpers by name: aclient_byte_dec and exists_zr_dec
   (the case splits, no classical axiom), aclient_vis (a client byte is visible, from ARm's am_client) and
   mem_some_of_aview_high (above the image a visible byte is a byte of m).  A non-client byte is present by AR's
   ahs_pres (YG0n.v:442) when hidden or outside ly_vis0, and by AR_states_vis0_shadow when visible and in ly_vis0. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YG0f Reusable.YG0n Reusable.YG0d.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YB1v Reusable.YE2k Reusable.YF0m B.AsanRT B.Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Prog.ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Local Open Scope Z_scope.
(* The core's sink_head instance (lib/Reusable/YE2k.v), named explicitly since YE2k is only Required (as
   B.ProgWorld does). *)
#[local] Existing Instance lib.Reusable.YE2k.tfib_sink_head.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

Section RtShadow.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* Premises and binder order as B.ProgWorld.RT_used_of_AR_stmt; CtrlTSyms and AR_laws are kept for that shape. *)
Lemma shadow_rw_of_AR :
  lib.Reusable.YF0m.CtrlTSyms B -> lib.Reusable.YG0d.AR_laws segs B -> B.ProgWorld.AR_states_vis0_shadow B ->
  forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md,
    lib.Reusable.YG0n.AR segs B ly S W m md -> B.AsanRT.shadow_rw m.
Proof.
  intros _ _ Hvis0 ly S W m md HAR a Hsh.
  pose proof HAR as (HM & _ & _ & _ & HPres & _).
  assert (Hband : lib.Reusable.YG0f.in_band_rw a).
  { unfold lib.Reusable.YG0f.in_band_rw, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kLowShadowEnd,
      lib.Reusable.YG0f.kHighShadowBeg, lib.Reusable.YG0f.kHighShadowEnd.
    unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hsh.
    destruct Hsh as [[H1 H2]|[H1 H2]]; [left|right]; lia. }
  assert (Hhigh : B.Prog.ImgBounds.IMG_HI <= a < 2 ^ 64).
  { unfold B.AsanRT.in_shadow, B.AsanRT.LOWMEM_END, B.AsanRT.LOWSHADOW_END, B.AsanRT.HIGHSHADOW_BEG,
      B.AsanRT.HIGHMEM_BEG in Hsh.
    unfold B.Prog.ImgBounds.IMG_HI.
    change (2 ^ 64) with 18446744073709551616.
    destruct Hsh as [[H1 H2]|[H1 H2]]; lia. }
  assert (Hm : m (Z_to_bv 64 a) <> None).
  { destruct (B.ProgWorldCtlRt.aclient_byte_dec B ly S a) as [Hcl|Hcl].
    - apply (B.ProgWorldCtlRt.mem_some_of_aview_high W m a Hhigh).
      exact (B.ProgWorldCtlRt.aclient_vis B ly S _ a (lib.Reusable.YG0n.am_client _ _ _ _ HM) Hcl).
    - destruct (B.ProgWorldCtlRt.exists_zr_dec a (lib.Reusable.YG0f.ly_vis0 ly)) as [Hv|Hv].
      + destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:EH.
        * exact (HPres a Hband Hcl (or_introl EH)).
        * exact (Hvis0 ly S W m md HAR a Hsh Hv EH).
      + exact (HPres a Hband Hcl (or_intror Hv)). }
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exfalso; exact (Hm eq_refl)].
  split.
  - unfold wview, lib.Lib.Mem.wa. rewrite Em. discriminate.
  - exists b. unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite Em. reflexivity.
Qed.

End RtShadow.

Print Assumptions shadow_rw_of_AR.
