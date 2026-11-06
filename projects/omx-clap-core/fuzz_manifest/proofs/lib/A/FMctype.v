(* fm's runtime contract for musl isalnum (0x88350) in the donor's form, aisalnum_realizes (FMH_Rt.v:169),
   from the register-only walk A/Prog/isalnum.v isalnum_holds through the generic lift FMrt_lift.v.
   musl tolower has no statement in FMH_Rt.v (fm reaches it only on the strncasecmp interceptor's
   not-yet-initialised branch), so it has none here.  The one Section hypothesis is the donor's
   `AR_laws tfibsegs B`, as the donor's own runtime walks take it (cgif_file A/AE2j.v:63). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v FMupoison FMH_Base FMH_Rt FMrt_lift.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require FMspec_str.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require isalnum_c isalnum.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem aisalnum_holds : aisalnum_realizes tfibsegs B PC_isalnum.
Proof.
  unfold aisalnum_realizes. intros ly S W regs mem md c HPRE G10 Hc.
  set (v := if isalnum_c.alnum_b c then 1 else 0).
  eapply srr_of_canon.
  - unfold canon_at. eapply isalnum.isalnum_holds; [exact Hc | exact G10].
  - intros ms0 ms' model' (a1' & ->) Heqv Hsbm _.
    eapply (rt_post_ro_win B LAWS STK_RT_ISALNUM 0 ly S W regs mem md _ _ ms' model' v HPRE
              ltac:(unfold STK_RT_ISALNUM, ESTACK; lia) Heqv Hsbm);
      try reflexivity.
    + keep_regs.
    + unfold v. destruct (isalnum_c.alnum_b c); lia.
    + unfold v. rewrite (FMspec_str.alnum_b_is_alnum c).
      destruct (ManifestModel.is_alnum c); split; intros H; [reflexivity | lia | lia | discriminate].
    + intros a Ha. lia.
Qed.

End i.
