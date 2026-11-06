(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the MEMSET Section
   hypothesis of the cno A' walk of check_no_overread, discharged at the concrete instance PI_prog_A by citation of the
   proved __asan_memset row. Lane CnoABatch2.MsetCite.
   rule 24: proves no function (kind: segment lemma of check_no_overread's walk: the MEMSET premise discharged by citation of the proved __asan_memset row)
   THE PREMISE (lib/A/Prog/Cno102A_R5.v and lib/A/Prog/Cno102A_R.v, their Section hypothesis MEMSET, generic over
   {PA : PAImg A_prog_listing}, with SEGS := @pa_segs _ A_prog_listing PA, SIGMA := @pa_sigma _ A_prog_listing PA):
     Hypothesis MEMSET : forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS B ARx OSet (SIGMA AS___asan_memset).
   THE CITATION: a working branch 599a4cefc740, lib/A/PRowSet.v (blob 4eac5264e9e8) :4373
     prow_asan_memset_xm_A : forall B ARx hl, YCbqG.AR_laws_x tfibsegs B ARx hl -> TfibSyms B ->
                             aintrin_realizes_xm tfibsegs B ARx OSet (pc_asan_memset (as_code B))
   (Section rows, Context {fx} {rc}: generic in the float state), taken by path with lib/A/PRowKitA.v a85a761d555d,
   lib/Reusable/PRowKit.v bdadcc818283 and the memcpy files lib/A/PRowCpy.v eeec9ca90589, PRowCpyA.v 6b5b462508d5,
   PRowCpyI.v 0d5053b908d6 (the previous commit). The one extra premise the citation needs is the row's own binding of
   B, A/AF0m.v's TfibSyms B (it gives as_code B = Tfib_code, A/AF0l.v dfca6bb1a8d7, so pc_asan_memset (as_code B) =
   0x52880); hl is the walk's cf_head.
   THE INSTANCE: lib/A/PAImg_prog.v (blob 505a51ff7d08) :405 PI_prog_A, pa_segs := rsegs of lib/A/Img0.v (blob
   84c90444e0b2) = images.Asan.M.loaded_segments, pa_sigma := A_prog_sigma (:105 AS___asan_memset => 0x52880).
   GUARDS (by reflexivity; every segment / listing / image name below is written fully qualified, since a closure that
   also loads the plain lib/Img0.v resolves the short Img0.rsegs to the plain image):
     cn_mset_segs   : pa_segs of PI_prog_A = lib.A.AB1v.tfibsegs (blob 5c16133beeff), the row's segments; both are
                      images.Asan.M.loaded_segments;
     cn_mset_sigma  : pa_sigma of PI_prog_A at AS___asan_memset = 0x52880;
     cn_mset_row_pc : pc_asan_memset of lib.A.AF0l.Tfib_code = 0x52880, the row's entry after TfibSyms.
   In this file's closure (#102 pins build), `Locate rsegs.` finds only lib.A.Img0.rsegs and `Locate tfibsegs.` only
   lib.A.AB1v.tfibsegs: the plain lib/Img0.v is not loaded here.
   No new step, no walk, no Admitted / Axiom. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YA0n YG00 YG0f YG0d YM05 YCbqG YGcfNames YGcallMxmn YC4aP YPsym.
(* Required, not Imported: every image-side name is cited fully qualified. *)
From OSSVerify.omx_clap_core.fuzz_preset.images Require Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Img0 Listing_prog PAImg_prog AB1v AF0l AF0m PRowSet.
Open Scope Z_scope.

Section ms. Context {rc : YM05.RunCeil} {cp : CfParams}.
Local Abbreviation SEGS := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YC4aP.pa_segs _
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A).
Local Abbreviation SIGMA := (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YC4aP.pa_sigma _
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Listing_prog.A_prog_listing
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A).

(* GUARD: the instance's segments are the row's tfibsegs (both images.Asan.M.loaded_segments) *)
Lemma cn_mset_segs : SEGS = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AB1v.tfibsegs.
Proof. reflexivity. Qed.

(* GUARD: the instance's __asan_memset is the row's entry *)
Lemma cn_mset_sigma : SIGMA OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YPsym.AS___asan_memset = 0x52880.
Proof. reflexivity. Qed.

(* GUARD: the row's entry, pc_asan_memset (as_code B) under TfibSyms B *)
Lemma cn_mset_row_pc : pc_asan_memset OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0l.Tfib_code = 0x52880.
Proof. reflexivity. Qed.

(* MEMSET of Cno102A_R5.v / Cno102A_R.v at PA := PI_prog_A, by citation of PRowSet.prow_asan_memset_xm_A *)
Theorem cn_memset_A : forall (B : asyms)
  (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop),
  AR_laws_x SEGS B ARx cf_head ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0m.TfibSyms B ->
  forall fz : YK11.FPState,
  aintrin_realizes_xm (fx := fz) SEGS B ARx OSet
    (SIGMA OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YPsym.AS___asan_memset).
Proof.
intros B ARx LAWS TB fz.
pose proof (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRowSet.prow_asan_memset_xm_A (fx := fz)
  B ARx cf_head LAWS TB) as ROW.
rewrite (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AF0m.ts_code B TB), cn_mset_row_pc in ROW.
rewrite cn_mset_sigma.
exact ROW.
Qed.
End ms.
