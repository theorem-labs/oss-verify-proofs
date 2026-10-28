(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegRunStrlen. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0Sums_b Ba0SumsStrlen_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Theorem as0_plan_sound_it :
  forall (IT : itab), itab_sound RSEGS IT ->
  forall (BFUEL : nat) (nx0 : nat) (BR : list SGP.bfact)
         (XSTEP : list SGP.region -> nat -> sym_state -> option sym_state) (F : list SGP.region) PSS p pc0 sr0 kn0,
  SGP.cert_ok RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none F PSS p pc0 sr0 kn0 = true ->
  (forall M0, SGP.XSTEP_ok RSEGS nx0 BR XSTEP F M0) ->
  forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok RSEGS E M kn0 -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' F
    /\ (forall a : word, SGP.outside E' F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok RSEGS E' M' K)
    /\ mem_grows M M'.
Proof.
  intros IT HIT BFUEL nx0 BR XSTEP F PSS p pc0 sr0 kn0 Hc HXS fx E R M HR HK HBF.
  exact (SGP.plan_entry_sound RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none
           HIT as0_copy_spec_memcpy as0_fill_spec_memset
           (SRS.strlen_step_sound _ _ _ _ as0_strlen_spec) as0_in_hull as0_hull_ok
           F PSS p pc0 sr0 kn0 fx E R M Hc HXS (fun M0 => SGP.xstep2_none_ok RSEGS nx0 BR F M0) HR HK HBF).
Qed.
