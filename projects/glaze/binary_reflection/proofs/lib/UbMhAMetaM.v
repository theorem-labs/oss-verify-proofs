(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhRsegs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rsegs_region_free_img : forall maps (a n : word),
  region_free (segments_reserved RSEGS ++ maps) a n = true -> 0 < bv_unsigned n ->
  bv_unsigned a + bv_unsigned n <= IMG_LO \/ IMG_HI <= bv_unsigned a.
Proof.
  intros maps a n Hrf Hn.
  assert (SEG : forall b s, In (Z_to_bv 64 b, Z_to_bv 64 s) (segments_reserved RSEGS) -> 0 <= b < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
            bv_unsigned a + bv_unsigned n <= b \/ b + s <= bv_unsigned a).
  { intros b s Hin Hb Hs. pose proof (region_free_In _ a n (Z_to_bv 64 b) (Z_to_bv 64 s) Hrf ltac:(apply in_app_iff; left; exact Hin)) as D.
    rewrite !u64_lit in D by lia. exact D. }
  rewrite rsegs_val in SEG.
  pose proof (SEG 0x10000 0x1e000 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as D1.
  pose proof (SEG 0x2e000 0x47000 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as D2.
  pose proof (SEG 0x75000 0x4000 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as D3.
  pose proof (SEG 0x79000 0x33000 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as D4.
  pose proof (u64_range a). lia.
Qed.

Section WithRun.
  Context {RN : run_ceil}.
  (* [comment removed for export] *)
  Lemma grant_range_hz : forall (h : VmMaps) maps (a n : word),
    page_floor (alloc_top h) = CEIL ->
    region_free (segments_reserved RSEGS ++ maps) a n = true -> 0 < bv_unsigned n ->
    bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
    bv_unsigned a + bv_unsigned n <= alloc_top h ->
    bv_unsigned a + bv_unsigned n <= CEIL /\ (bv_unsigned a + bv_unsigned n <= IMG_LO \/ IMG_HI <= bv_unsigned a).
  Proof using.
    intros h maps a n Htop Hrf Hn Hal Hnl Hle. split.
    - apply (grant_end_le_CEIL h (bv_unsigned a) (bv_unsigned n) Htop); try assumption.
      rewrite Z.add_mod, Hal, Hnl by lia. reflexivity.
    - exact (rsegs_region_free_img maps a n Hrf Hn).
  Qed.
End WithRun.
End UbMhRsegs.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module UbMhAMetaWF.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.LibAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Z.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can : Z) (ra s0v s1v s2v s3v s4v : word).
  Hypothesis Hsp : (CEIL + 64 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis Hra : ret_ok ra.
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_c56 : rdn RSEGS m (Z_to_bv 64 (sp - 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_ra : rdn RSEGS m (Z_to_bv 64 (sp - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m (Z_to_bv 64 (sp - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m (Z_to_bv 64 (sp - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m (Z_to_bv 64 (sp - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m (Z_to_bv 64 (sp - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).
  Hypothesis M_s4 : rdn RSEGS m (Z_to_bv 64 (sp - 48)) 8%nat = Some (word_to_le_bytes 8 s4v).

  Definition clobZ : list reg := [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%bv.

  Ltac epilogue H2 :=
    stepLD8 F_66e90 D_66e90 (Z_to_bv 64 can);
    stepLD8 F_66e94 D_66e94 (Z_to_bv 64 can);
    stepb_ft F_66e98 D_66e98 ltac:(apply c_eq_refl || (rewrite c_eq_Z by lia; apply Z.eqb_refl));
    stepLD8 F_66e9c D_66e9c ra;
    stepLD8 F_66ea0 D_66ea0 s0v;
    stepLD8 F_66ea4 D_66ea4 s1v;
    stepLD8 F_66ea8 D_66ea8 s2v;
    stepLD8 F_66eac D_66eac s3v;
    stepLD8 F_66eb0 D_66eb0 s4v;
    stepn F_66eb4 D_66eb4; rewrite H2; addi_renorm;
    stepret F_66eb8 D_66eb8 ra ltac:(reflexivity).


  (* [comment removed for export] *)
  Lemma amM2f : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 18 = Z_to_bv 64 A_CANARY ->
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 20 = Z_to_bv 64 (2^64 - 1) ->
    exists regs',
      msteps RSEGS (mkst regs (0x66e4c : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clobZ regs regs'.
  Proof using M_s4 M_s3 M_s2 M_s1 M_s0 M_ra M_c56 M_can Hra Hsp can RN.
    intros regs rom H2 H18 H10 H20. ceil; unfold HEAPLO, A_CANARY in *.
    eexists. split.
    - stepb_tk F_66df8 D_66df8 ltac:(rewrite H10, H20; apply c_eq_refl).
      stepn F_66ee0 D_66ee0.
      stepn F_66ee4 D_66ee4.
      epilogue H2.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Hypothesis M_errno : rdn RSEGS m (Z_to_bv 64 A_ERRNO) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 12)).
  Lemma amPf : forall regs rom,
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 18 = Z_to_bv 64 A_CANARY ->
    getr regs 10 = Z_to_bv 64 (2^64 - 1) -> getr regs 4 = Z_to_bv 64 TPV ->
    exists regs',
      msteps RSEGS (mkst regs (0x66f20 : word) m rom) (mkst regs' ra m rom)
      /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ keeps_but clobZ regs regs'.
  Proof using M_errno M_s4 M_s3 M_s2 M_s1 M_s0 M_ra M_c56 M_can Hra Hsp can RN.
    intros regs rom H2 H18 H10 H4. ceil; unfold HEAPLO, A_CANARY, A_ERRNO, TPV in *.
    eexists. split.
    - stepb_ft F_66ecc D_66ecc ltac:(rewrite H10; cond_compute).
      stepn F_66ed0 D_66ed0.
      stepn F_65ac4 D_65ac4. rewrite H4.
      stepn F_65ac8 D_65ac8. try addi_renorm.
      stepret F_65acc D_65acc (Z_to_bv 64 0x66f28) ltac:(reflexivity).
      stepLD F_66ed4 D_66ed4 (word_to_le_bytes 4 (Z_to_bv 64 12)) (Z_to_bv 64 12)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      try rewrite v_lw_s32 by lia.
      stepn F_66ed8 D_66ed8.
      stepb_ft F_66edc D_66edc ltac:(cond_compute).
      stepn F_66ee0 D_66ee0.
      stepn F_66ee4 D_66ee4.
      epilogue H2.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption. all: try (f_equal; lia). all: solve_keeps_but.
  Qed.
End Z.
End UbMhAMetaWF.
Require Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhAMetaT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhBrkK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhAMetaW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF.UbMhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac tr_clear_heavy := repeat match goal with
  | H : context [Z.max _ _] |- _ => clear H | H : context [Z.min _ _] |- _ => clear H
  | H : context [Z.div _ _] |- _ => clear H | H : context [Z.modulo _ _] |- _ => clear H end.
#[local] Ltac lia_fast ::= first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ].
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
#[local] Ltac mh_lia_nx := rnfix; first [ solve [hclr; lean zlia] | pa_arith_concl; lia_goal_ok; lia_hsep; first [ with_img1f_ zlia | with_img1_ zlia | lia_pairs; with_img2 zlia ] ].
#[local] Ltac lia ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | mh_lia_nx ].
#[local] Ltac lia_fast ::= first [ solve [ rnfix; pa_tiers ltac:(zlia) ] | solve [ rnfix; pa_big; lia_goal_ok; lia_hsep; pa_tierB ltac:(zlia) ] | first [ solve [ clear_disj; tr_clear_heavy; lia ] | solve [ clear_disj; lia ] | lia ] ].
Section MemHelp2.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Lemma wbytes_get_inside : forall bs (Mb : mem) (addr x : word),
    bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64 ->
    bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + Z.of_nat (length bs) ->
    wbytes Mb addr bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned addr)).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    induction bs as [|b rest IH]; intros Mb addr x Hnw Hx; cbn [wbytes length] in *; [lia|].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned addr)) as [E|Hne].
    - assert (Ex : x = addr) by (apply bv_eq; exact E). subst x. rewrite Z.sub_diag. cbn.
      destruct rest as [|b' rest'].
      + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
      + assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
        rewrite wbytes_below by (cbn [length] in *; lia). cbv beta. rewrite bv_eqb_refl. reflexivity.
    - destruct rest as [|b' rest']; [cbn [length] in Hx; lia|].
      assert (Hu1 : bv_unsigned (addr + 1)%bv = bv_unsigned addr + 1) by (apply u_add1; cbn [length] in Hnw; lia).
      rewrite IH by (cbn [length] in *; lia). rewrite Hu1.
      replace (Z.to_nat (bv_unsigned x - bv_unsigned addr)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned addr + 1)))) by lia.
      reflexivity.
  Qed.

  Lemma wbytes_z8_inside : forall (Mb : mem) a0 x, 0 <= a0 -> a0 + 8 < 2 ^ 64 -> a0 <= x < a0 + 8 ->
    wbytes Mb (Z_to_bv 64 a0) (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a0 x H0 H8 Hx.
    rewrite wbytes_get_inside by (wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
    rewrite !u_Z2bv by lia.
    assert (E : x - a0 = 0 \/ x - a0 = 1 \/ x - a0 = 2 \/ x - a0 = 3 \/ x - a0 = 4 \/ x - a0 = 5 \/ x - a0 = 6 \/ x - a0 = 7) by lia.
    destruct E as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma wbytes_outZ : forall (Mb : mem) b bs a, 0 <= b -> b + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
    ~ (b <= a < b + Z.of_nat (length bs)) -> wbytes Mb (Z_to_bv 64 b) bs (Z_to_bv 64 a) = Mb (Z_to_bv 64 a).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb b bs a Hb Hbl Ha Hout. destruct (decide (wbytes Mb (Z_to_bv 64 b) bs (Z_to_bv 64 a) = Mb (Z_to_bv 64 a))) as [E|NE]; [exact E|].
    exfalso. apply Hout. exact (wbytes_diff_g Mb b bs a Hb Hbl Ha NE).
  Qed.

  Lemma zfill_diffZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
    zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) <> Mb (Z_to_bv 64 x) -> a <= x < a + n.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a n x Ha Hn Han Hx NE. destruct (decide (a <= x < a + n)) as [IN|OUT]; [exact IN|]. exfalso. apply NE.
    apply zfill_out. rewrite !u_Z2bv by lia. lia.
  Qed.
  Lemma zfill_inZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> a <= x < a + n ->
    zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) = Some (Z_to_bv 8 0).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a n x Ha Hn Han Hx. unfold zfill, zmem. rewrite !u_Z2bv by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  Qed.
  Lemma zfill_grows : forall (a n : word) (Mb : mem), mem_grows Mb (zfill a n Mb).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros a n Mb x Hx. unfold zfill, zmem. destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.
  Lemma unfill_diffZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
    unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) <> Mb (Z_to_bv 64 x) -> a <= x < a + n.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a n x Ha Hn Han Hx NE. destruct (decide (a <= x < a + n)) as [IN|OUT]; [exact IN|]. exfalso. apply NE.
    apply unfill_out. rewrite !u_Z2bv by lia. lia.
  Qed.
  Lemma unfill_outZ : forall (Mb : mem) a n x, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x < 2 ^ 64 -> ~ (a <= x < a + n) ->
    unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb (Z_to_bv 64 x) = Mb (Z_to_bv 64 x).
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. intros Mb a n x Ha Hn Han Hx OUT. apply unfill_out. rewrite !u_Z2bv by lia. lia. Qed.
  Lemma rdn_zfill_outZ : forall (Mb : mem) a n x k, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= a \/ a + n <= x) ->
    rdn RSEGS (zfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb) (Z_to_bv 64 x) k = rdn RSEGS Mb (Z_to_bv 64 x) k.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a n x k Ha Hn Han Hx Hk D. destruct k as [|k']; [reflexivity|].
    apply rdn_zfill_out; rewrite !u_Z2bv by lia; lia.
  Qed.
  Lemma rdn_unfill_outZ : forall (Mb : mem) a n x k, 0 <= a -> 0 <= n -> a + n < 2 ^ 64 -> 0 <= x -> x + Z.of_nat k <= 2 ^ 64 ->
    (x + Z.of_nat k <= a \/ a + n <= x) ->
    rdn RSEGS (unfill (Z_to_bv 64 a) (Z_to_bv 64 n) Mb) (Z_to_bv 64 x) k = rdn RSEGS Mb (Z_to_bv 64 x) k.
  Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end.
    intros Mb a n x k Ha Hn Han Hx Hk D. destruct k as [|k']; [reflexivity|].
    apply rdn_unfill_out; rewrite !u_Z2bv by lia; lia.
  Qed.
End MemHelp2.

Section AMC. (* [comment removed for export] *)
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp : Z) (Q : config -> Prop).
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGERX st X (m_vmmaps mdl).
  Hypothesis XOK : xok X.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HCNT : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HLEN : Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246.
  Hypothesis HBUD : XSUM X + RSUM (s_regions st) + 2 ^ 24 <= vm_limit (m_vmmaps mdl).
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Hra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis DEF : defined M (sp - AMSTK) sp.
  Hypothesis HQ : forall c', am_post st L X sp regs M mdl rom c' -> Q c'.

  #[local] Notation cx := (s_ctx st).
  #[local] Notation can := (UbMhAMetaS.can st).
  #[local] Notation M1 := (UbMhAMetaS.M1 st M regs sp).
  #[local] Notation tl := (c_area_tail (s_ctx st)).
  #[local] Notation sec := (c_secret (s_ctx st)).

  (* [comment removed for export] *)
  Definition ctxV (a : Z) : Prop :=
    (ctx_avail_meta_area_count <= a < ctx_avail_meta_area_count + 16) \/ (ctx_avail_meta_areas <= a < ctx_avail_meta_areas + 8) \/
    (ctx_brk <= a < ctx_brk + 8).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dfoot_rng : forall a, dfoot st a -> 0 <= a < 2 ^ 64.
  Proof using HWF X L RN. clear - HWF X L RN.
    intros a [Fa|[Fa|[(ar & Har & Fa)|(x & Hx & Kx & Fa)]]]; unfold A_ERRNO, TPV, CTX_END, CTX in *; try lia.
    - destruct (wa_rng st (WF_areas st L HWF) ar Har) as (_ & R1 & R2). ceil; unfold HEAPLO in *. lia.
    - destruct (group_range st L HWF x Hx) as [R _].
      pose proof (wg_kind st L x (wG_each st L (WF_groups st L HWF) x Hx)) as KD. rewrite Kx in KD.
      destruct KD as (_ & Kreg & _). destruct (wr_rng st (WF_regions st L HWF) _ Kreg) as (_ & R2 & _). cbn in R2.
      ceil; unfold HEAPLO in *. lia.
  Qed.

  Section Tail.
    Variables (rT : bvmap 5 word) (MT : mem) (mdlT : Model) (p : Z) (regions' : list region) (brk' : brk_state) (acT sh' cb' eT : Z)
              (NB : Z -> Prop) (bigT : list reg).
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    (* [comment removed for export] *)
    Hypothesis T2 : getr rT 2 = Z_to_bv 64 (sp - 64).
    Hypothesis T9 : getr rT 9 = Z_to_bv 64 p.
    Hypothesis T19 : getr rT 19 = Z_to_bv 64 MLOCK.
    Hypothesis T18 : getr rT 18 = Z_to_bv 64 A_CANARY.
    Hypothesis T21 : getr rT 21 = getr regs 21.
    Hypothesis KT : keeps_but bigT regs rT.
    Hypothesis COVT : forallb (fun r => existsb (fun x => bv_eqb x r) AM_CLOB || existsb (fun x => bv_eqb x r) AM_SAVED)%bool bigT = true.
    Hypothesis Th : m_halted mdlT = None.
    Hypothesis Tlz : m_vm_lazy mdlT = [].
    Hypothesis Tmat : m_vm_materialized mdlT = [].
    Hypothesis Tfs : m_fs mdlT = m_fs mdl.
    Hypothesis Tfds : m_fds mdlT = m_fds mdl.
    Hypothesis Tlim : vm_limit (m_vmmaps mdlT) = vm_limit (m_vmmaps mdl).
    (* [comment removed for export] *)
    Hypothesis TW : forall a, 0 <= a < 2 ^ 64 -> MT (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ ctxV a \/ NB a \/ (A_ERRNO <= a < A_ERRNO + 4).
    (* [comment removed for export] *)
    Hypothesis TE : cell MT A_ERRNO 4 eT.
    Hypothesis TED : forall a, A_ERRNO <= a < A_ERRNO + 4 -> MT (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> MT (Z_to_bv 64 a) <> None.
    Hypothesis HeT : eT = s_errno st \/ eT = 12.
    Hypothesis NBfacts : forall a, NB a -> HEAPLO <= a /\ a < CEIL /\ (forall ar, In ar (s_areas st) -> ~ (ar <= a < ar + 4096)) /\
                                   (forall t, is_group st t -> s_kind st t = GTop -> ~ (g_mem st t <= a < g_map_end st t)).
    (* [comment removed for export] *)
    Hypothesis NBreg : forall a, NB a -> (exists r, In r regions' /\ (forall x, rg_kind r <> RGroup x) /\ rg_base r <= a < rg_base r + rg_len r) \/
                                     am_holeR regions' X a.
    Hypothesis TKeep : forall a, dfoot st a -> M (Z_to_bv 64 a) <> None -> MT (Z_to_bv 64 a) <> None.
    Hypothesis TPage : forall a, p <= a < p + 4096 -> MT (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
    Hypothesis TDef : defined MT (sp - AMSTK) sp.
    Hypothesis Tac : cell MT ctx_avail_meta_area_count 8 acT.
    Hypothesis Tsh : cell MT ctx_meta_alloc_shift 8 sh'.
    Hypothesis Tcb : cell MT ctx_brk 8 cb'.
    Hypothesis TacR : 0 < acT < 2 ^ 63.
    (* [comment removed for export] *)
    Hypothesis Hp : p mod 4096 = 0 /\ HEAPLO <= p /\ p + 4096 <= CEIL.
    Hypothesis Hp_img : img_free p (p + 4096).
    Hypothesis Hp_areas : forall a, In a (s_areas st) -> a + 4096 <= p \/ p + 4096 <= a.
    Hypothesis Hp_groups : forall x, is_group st x -> gspan st x <= p \/ p + 4096 <= g_mem st x.
    Hypothesis Hcnt : Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
    Hypothesis HRgrp : forall b len x, In (RG b len (RGroup x)) regions' <-> In (RG b len (RGroup x)) (s_regions st).
    Hypothesis HRsub : forall r, In r (s_regions st) -> exists r', In r' regions' /\ rg_base r' = rg_base r /\ rg_len r' = rg_len r.
    Hypothesis HRold : forall a, In a (s_areas st) -> INREG regions' brk' a.
    Hypothesis HRnew : INREG regions' brk' p.
    Hypothesis Hcur' : acT - 1 > 0 -> exists b len e, In (RG b len (RMeta e)) regions' /\ 0 <= e /\
                         p + 4096 = b + 4096 * (1 + e) /\ p + 4096 + 4096 * (acT - 1) = b + len.
    Hypothesis Hsh' : 0 <= sh' /\ sh' <= Z.of_nat (length (s_areas st)) + 2 /\ (acT - 1 = 0 -> sh' <= Z.of_nat (length (s_areas st)) + 1).
    Hypothesis Hshacc' : 2 ^ (sh' + 1) <= Z.of_nat (length (s_areas st)) + 1 + (acT - 1) + sh' + 2.
    Hypothesis Hbrk' : match brk' with
                       | BrkUntried => cb' = 0
                       | BrkLive b0 b _ => cb' = b /\ b0 mod 4096 = 0 /\ b mod 4096 = 0 /\ IMG_HI <= b0 /\ b0 + 8192 <= b /\ b <= CEIL
                       | BrkDead _ => cb' = 2 ^ 64 - 1
                       end.
    #[local] Notation stN := (UbMhAMetaN.st' st p regions' brk' (acT - 1) sh' cb').
    Hypothesis HWR' : wf_regions stN.
    Hypothesis HWI' : wf_img stN.
    Hypothesis HLG' : LEDGERX stN X (m_vmmaps mdlT).
    Hypothesis HRS : RSUM regions' <= RSUM (s_regions st) + 2 ^ 24.
    Hypothesis HRL : Z.of_nat (length regions') <= Z.of_nat (length (s_regions st)) + 1.
    Hypothesis HRX : forall r, In r regions' -> (exists r0, In r0 (s_regions st) /\ rg_base r0 = rg_base r /\ rg_len r0 = rg_len r) \/
         forall e, In e X -> exists ea en, e = (Z_to_bv 64 ea, Z_to_bv 64 en) /\ HEAPLO <= ea /\ 0 < en /\ ea + en <= CEIL /\ (rg_base r + rg_len r <= ea \/ ea + en <= rg_base r).

    Hypothesis Hp_maps : forall t, is_group st t -> s_kind st t = GTop -> g_map_end st t <= p \/ p + 4096 <= g_mem st t.
    Hypothesis TStack : forall a n bs, sp - 56 <= a -> a + Z.of_nat n <= sp ->
      rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS MT (Z_to_bv 64 a) n = Some bs.

    Lemma tl_is : tl = last (s_areas st) 0. Proof using HWF L RN. clear - HWF L RN. exact (wc_tail st (WF_ctx st L HWF)). Qed.
    Lemma tl_cases : (s_areas st = [] /\ tl = 0) \/ (s_areas st <> [] /\ In tl (s_areas st) /\ tl mod 4096 = 0 /\ HEAPLO <= tl /\ tl + 4096 <= CEIL).
    Proof using Hshacc' Hsh' HRold Hcnt Hp_areas NBfacts NB sh' acT brk' regions' p HCNT HWF L. clear - Hshacc' Hsh' HRold Hcnt Hp_areas NBfacts NB sh' acT brk' regions' p HCNT HWF L.
      rewrite tl_is. destruct (s_areas st) as [|a l] eqn:E; [left; split; reflexivity | right].
      assert (NE : s_areas st <> []) by (rewrite E; discriminate).
      assert (Hin : In (last (s_areas st) 0) (s_areas st)) by (apply In_last; exact NE).
      rewrite E in Hin. split; [discriminate|]. split; [exact Hin|]. rewrite <- E in Hin |- *. exact (wa_rng st (WF_areas st L HWF) _ Hin).
    Qed.

    (* [comment removed for export] *)
    Lemma NB_not_img : forall y, IMG_LO <= y < IMG_HI -> ~ NB y.
    Proof using HWI' Hsh' TacR NBreg cb' sh' acT brk' regions' p X st RN. clear - HWI' Hsh' TacR NBreg cb' sh' acT brk' regions' p X st RN.
      intros y Hy N. destruct (NBreg y N) as [(r & Hr & _ & R)|H]; [|destruct H as (_ & Hi & _); lia].
      pose proof (wi_regions _ HWI' r Hr) as D. unfold img_free in D. lia.
    Qed.
    (* [comment removed for export] *)
    Lemma T_agree : forall a n v, IMG_LO <= a -> A_ERRNO + 4 <= a -> a + Z.of_nat n <= IMG_HI ->
      (forall y, a <= y < a + Z.of_nat n -> ~ ctxV y) -> cell M a n v -> cell MT a n v.
    Proof using HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp sp X st RN. clear - HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp sp X st RN.
      intros a n v Ha Hae Hn OUT C. pose proof Hsp as [S1 S2]. eapply cell_agree; [lia | lia | | exact C].
      intros y Hr Hy. destruct (decide (MT (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      destruct (TW y Hr NE) as [W|[W|[W|W]]].
      - ceil; unfold AMSTK in *. lia.
      - exact (OUT y Hy W).
      - apply (NB_not_img y); [lia | exact W].
      - lia.
    Qed.
    Ltac ctx_out := unfold ctxV, ctx_secret, ctx_meta_area_tail, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, ctx_meta_alloc_shift,
                      ctx_avail_meta, ctx_avail_meta_count, ctx_meta_area_head, ctx_free_meta_head, A_CANARY, CTX, CTX_END in *; cbn; intros; lia.
    Lemma T_sec : cell MT ctx_secret 8 sec.
    Proof using HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN. clear - HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN. apply T_agree; [unfold ctx_secret, CTX; lia | unfold ctx_secret, CTX, A_ERRNO, TPV; lia | unfold ctx_secret, CTX; cbn; lia | ctx_out | exact (rc_secret st M (rp_ctx st M HREP))]. Qed.
    Lemma T_tl : cell MT ctx_meta_area_tail 8 tl.
    Proof using HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN. clear - HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN. apply T_agree; [unfold ctx_meta_area_tail, CTX; lia | unfold ctx_meta_area_tail, CTX, A_ERRNO, TPV; lia | unfold ctx_meta_area_tail, CTX; cbn; lia | ctx_out | exact (rc_mat st M (rp_ctx st M HREP))]. Qed.
    Lemma T_can : rdn RSEGS MT (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
    Proof using HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN. clear - HWI' Hsh' TacR NBreg TW NB cb' sh' acT brk' regions' p Hsp HREP sp M X RN.
      pose proof (rc_canary st M (rp_statics st M HREP)) as C. unfold UbMhAMetaS.can.
      apply T_agree; [unfold A_CANARY; lia | unfold A_CANARY, A_ERRNO, TPV; lia | unfold A_CANARY; cbn; lia | ctx_out | exact C].
    Qed.
    Lemma T_sokc : store_ok RSEGS MT (Z_to_bv 64 CTX) 928%nat = true.
    Proof using TKeep M st. clear - TKeep M st. pose proof TKeep as _K. apply store_ok_wseg. vm_compute. reflexivity. Qed.
    Lemma T_sokp : store_ok RSEGS MT (Z_to_bv 64 p) 4096%nat = true.
    Proof using Hsh' Hp TacR TPage sh' acT regions' X st RN. clear - Hsh' Hp TacR TPage sh' acT regions' X st RN.
      destruct Hp as (P0 & P1 & P2). ceil; unfold HEAPLO in P1, P2.
      eapply (store_ok_defined MT p (p + 4096)); [| lia | cbn; lia | lia | lia].
      intros a Ha. rewrite (TPage a Ha). discriminate.
    Qed.
    Lemma T_soktl : s_areas st <> [] -> store_ok RSEGS MT (Z_to_bv 64 (tl + 8)) 8%nat = true.
    Proof using Hshacc' Hsh' HRold Hcnt Hp_areas TacR TKeep NBfacts NB sh' acT brk' regions' p HCNT HREP HWF M X L RN. clear - Hshacc' Hsh' HRold Hcnt Hp_areas TacR TKeep NBfacts NB sh' acT brk' regions' p HCNT HREP HWF M X L RN.
      intros NE. destruct tl_cases as [[E _]|(_ & Hin & Tal & Tlo & Thi)]; [exfalso; exact (NE E)|]. ceil; unfold HEAPLO in Tlo, Thi.
      eapply (store_ok_defined MT tl (tl + 4096)); [| lia | cbn; lia | lia | lia].
      intros a Ha. apply TKeep; [right; right; left; exists tl; split; [exact Hin | exact Ha] | exact (ra_def st M tl (rp_areas st M HREP tl Hin) a Ha)].
    Qed.

    (* [comment removed for export] *)
    Lemma T_run : exists rf Mf,
      msteps RSEGS (mkst rT (0x66e80%bv : word) MT rom) (mkst rf (0x66edc%bv : word) Mf rom) /\
      getr rf 10 = Z_to_bv 64 (p + 24) /\ keeps_but [10; 11; 12]%bv rT rf /\
      Mf = m_Ttail p sec (wbytes (m_T0 MT p acT) (Z_to_bv 64 (if (s_areas st) then ctx_meta_area_head else tl + 8)) (word_to_le_bytes 8 (Z_to_bv 64 p))).
    Proof using HWI' Hshacc' Hsh' HRold Hcnt Hp_areas Hp_img Hp TacR Tac TPage TKeep NBreg NBfacts TW T19 T9 NB cb' sh' brk' regions' Hsp HCNT HREP HWF sp M X L RN. clear - HWI' Hshacc' Hsh' HRold Hcnt Hp_areas Hp_img Hp TacR Tac TPage TKeep NBreg NBfacts TW T19 T9 NB cb' sh' brk' regions' Hsp HCNT HREP HWF sp M X L RN.
      destruct Hp as (P0 & P1 & P2).
      destruct tl_cases as [[E Etl]|(NE & Hin & Tal & Tlo & Thi)].
      - destruct (amTn MT p acT tl sec ltac:(unfold img_free in Hp_img; clear -Hp Hp_img; (first [ (clear NBreg HeT TW; lia) | lia ])) TacR ltac:(rewrite Etl; ceil; (first [ (clear P0 Hp_maps Hp_groups Hp_areas NBreg HeT TW; lia) | lia ])) Tac T_tl T_sec T_sokc
                    ltac:(eapply (store_ok_sub _ _ _ _ 4096%nat); [|exact T_sokp| |]; ceil; unfold HEAPLO in *; zsimp; (first [ (clear H0 HRX Hbrk' NBreg HeT TW; lia) | lia ])) rT rom T19 T9 Etl)
          as (rf & RUN & E10 & Kf).
        exists rf, (m_Tn MT p acT sec). rewrite E. repeat split; try assumption.
      - destruct (amTt MT p acT tl sec ltac:(unfold img_free in Hp_img; clear -Hp Hp_img; (first [ (clear Tal NBreg HeT TW; lia) | lia ])) TacR ltac:(unfold HEAPLO in *; (first [ (clear P0 Hp_maps Hp_groups Hp_areas NBreg HeT TW; lia) | lia ])) Tac T_tl T_sec T_sokc
                    ltac:(eapply (store_ok_sub _ _ _ _ 4096%nat); [|exact T_sokp| |]; ceil; unfold HEAPLO in *; zsimp; (first [ (clear H0 Tal HRX Hbrk' NBreg HeT TW; lia) | lia ])) rT rom T19 T9
                    ltac:(unfold HEAPLO in *; (first [ (clear P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ])) Tlo (area_img st L HWF tl Hin) (Hp_areas tl Hin) (T_soktl NE))
          as (rf & RUN & E10 & Kf).
        exists rf, (m_Tt MT p acT tl sec). destruct (s_areas st) as [|a0 l0] eqn:E; [exfalso; exact (NE eq_refl)|]. repeat split; try assumption.
    Qed.

    (* [comment removed for export] *)
    Definition tailW (a : Z) : Prop :=
      (ctx_avail_meta_area_count <= a < ctx_avail_meta_area_count + 8) \/ (ctx_avail_meta_areas <= a < ctx_avail_meta_areas + 8) \/
      (tl = 0 /\ ctx_meta_area_head <= a < ctx_meta_area_head + 8) \/ (ctx_meta_area_tail <= a < ctx_meta_area_tail + 8) \/ (tl <> 0 /\ tl + 8 <= a < tl + 16) \/
      (p <= a < p + 8) \/ (p + 16 <= a < p + 20) \/ (ctx_avail_meta <= a < ctx_avail_meta + 16) \/ (p + 24 <= a < p + 40).

    Theorem am_tail : kat RSEGS (mkCfg (mkst rT (0x66e80%bv : word) MT rom) mdlT) Q.
    Proof using TStack Hp_maps HRX HRL HRS HLG' HWI' HWR' Hbrk' Hshacc' Hsh' Hcur' HRnew HRold HRsub HRgrp Hcnt Hp_groups Hp_areas Hp_img Hp TacR Tcb Tsh Tac TDef TPage TKeep NBreg NBfacts HeT TED TE TW Tlim Tfds Tfs Tmat Tlz Th COVT KT T21 T18 T19 T9 T2 Hac0 Hfl bigT NB eT cb' sh' acT brk' regions' p HQ Hsp Hra H2 HCNT HREP HWF sp regs mdl M X L st RN. clear - TStack Hp_maps HRX HRL HRS HLG' HWI' HWR' Hbrk' Hshacc' Hsh' Hcur' HRnew HRold HRsub HRgrp Hcnt Hp_groups Hp_areas Hp_img Hp TacR Tcb Tsh Tac TDef TPage TKeep NBreg NBfacts HeT TED TE TW Tlim Tfds Tfs Tmat Tlz Th COVT KT T21 T18 T19 T9 T2 Hac0 Hfl bigT NB eT cb' sh' acT brk' regions' p HQ Hsp Hra H2 HCNT HREP HWF sp regs mdl M X L st RN.
      destruct Hp as (P0 & P1 & P2). pose proof Hsp as [S1 S2]. pose proof (UbMhAMetaS.can_rng st L HWF) as CANR.
      pose proof (wc_secret st (WF_ctx st L HWF)) as SECR. pose proof Hp_img as PI. unfold img_free in PI.
      destruct T_run as (rf & Mf & RUN & E10 & Kf & EMf).
      ceil; unfold HEAPLO, AMSTK in P1, P2, S1.
      assert (TLR : 0 <= tl /\ tl + 4096 <= CEIL /\ (s_areas st <> [] -> HEAPLO <= tl /\ (tl + 4096 <= IMG_LO \/ IMG_HI <= tl) /\ (tl + 4096 <= p \/ p + 4096 <= tl))).
      { destruct tl_cases as [[E Etl]|(NE & Hin & Tal & Tlo & Thi)]; [rewrite Etl; split; [lia|]; split; [ceil; lia|]; intros NE; exfalso; exact (NE E)|].
        split; [unfold HEAPLO in Tlo; lia|]. split; [exact Thi|]. intros _. split; [exact Tlo|]. split; [exact (area_img st L HWF tl Hin) | exact (Hp_areas tl Hin)]. }
      destruct TLR as (TL1 & TL2 & TL3a). unfold HEAPLO in TL3a.
      assert (TLNE : tl <> 0 -> s_areas st <> []) by (intros Hne E; destruct tl_cases as [[_ Etl]|(NE & _)]; [exact (Hne Etl) | exact (NE E)]).
      assert (TL3 : tl <> 0 -> 4096 <= tl /\ (tl + 4096 <= IMG_LO \/ IMG_HI <= tl) /\ (tl + 4096 <= p \/ p + 4096 <= tl)) by (intros Hne; exact (TL3a (TLNE Hne))).
      assert (TLZ : s_areas st = [] -> tl = 0) by (intros E; destruct tl_cases as [[_ Etl]|(NE & _)]; [exact Etl | exfalso; exact (NE E)]).
      (* [comment removed for export] *)
      assert (WT : forall a, 0 <= a < 2 ^ 64 -> Mf (Z_to_bv 64 a) <> MT (Z_to_bv 64 a) -> tailW a).
      { intros a Ha NE. rewrite EMf in NE. unfold tailW. unfold m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head,
          ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        destruct (s_areas st) as [|a0 l0] eqn:EA.
        - pose proof (TLZ eq_refl) as Etl. wdiff NE MT a.
        - assert (NE' : tl <> 0) by (intros E0; pose proof (TL3a ltac:(discriminate)) as [X1 _]; lia). pose proof (TL3 NE') as (TL4 & TL4i & TL5). wdiff NE MT a. }
      assert (GT : mem_grows MT Mf).
      { rewrite EMf. unfold m_Ttail, m_T0. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
      (* [comment removed for export] *)
      assert (STK : forall a n bs, sp - 56 <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS Mf (Z_to_bv 64 a) n = Some bs).
      { intros a n bs Ha Hn R. rewrite <- (TStack a n bs Ha Hn R). apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
        intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as Xr. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
        destruct (decide (Mf (Z_to_bv 64 (bv_unsigned x)) = MT (Z_to_bv 64 (bv_unsigned x)))) as [E|NE]; [exact E|]. exfalso.
        pose proof (WT (bv_unsigned x) ltac:(lia) NE) as W. unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, CTX in W. lia. }
      assert (CANf : rdn RSEGS Mf (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can))).
      { rewrite <- T_can. apply rdn_ext; [rewrite u_Z2bv by (unfold A_CANARY; lia); unfold A_CANARY; lia|].
        intros x Hx. rewrite u_Z2bv in Hx by (unfold A_CANARY; lia). unfold A_CANARY in Hx. pose proof (u64_range x) as Xr. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
        destruct (decide (Mf (Z_to_bv 64 (bv_unsigned x)) = MT (Z_to_bv 64 (bv_unsigned x)))) as [E|NE]; [exact E|]. exfalso.
        pose proof (WT (bv_unsigned x) ltac:(lia) NE) as W. unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, CTX in W. (first [ (clear H0 HRX Hbrk' HeT TW; lia) | lia ]). }
      assert (SOKg : store_ok RSEGS Mf (Z_to_bv 64 (p + 24)) 16%nat = true).
      { eapply store_ok_mono; [exact GT|]. eapply (store_ok_sub _ _ _ _ 4096%nat); [|exact T_sokp| |]; zsimp; (first [ (clear H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]). }
      destruct (amE Mf sp can (p + 24) (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)
                  ltac:(ceil; lia) ltac:(ceil; unfold HEAPLO; lia) Hra SOKg CANf
                  (STK (sp - 56) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_can st X M regs sp Hsp))
                  (STK (sp - 8) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_ra st X M regs sp Hsp))
                  (STK (sp - 16) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_s0 st X M regs sp Hsp))
                  (STK (sp - 24) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_s1 st X M regs sp Hsp))
                  (STK (sp - 32) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_s2 st X M regs sp Hsp))
                  (STK (sp - 40) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_s3 st X M regs sp Hsp))
                  (STK (sp - 48) 8%nat _ ltac:(lia) ltac:(cbn; lia) (UbMhAMetaS.M1_s4 st X M regs sp Hsp))
                  rf rom ltac:(kept_rw Kf; exact T2) E10 ltac:(kept_rw Kf; exact T18))
        as (r' & RUNE & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & KE).
      eapply kat_msteps; [exact Th | exact Tlz | exact RUN |]. eapply kat_msteps; [exact Th | exact Tlz | exact RUNE |].
      apply kat_refl. apply HQ.
      set (M' := m_E Mf (p + 24)).
      assert (WE : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> Mf (Z_to_bv 64 a) -> p + 24 <= a < p + 40).
      { intros a Ha NE. unfold M', m_E in NE. wdiff NE Mf a. }
      assert (GE : mem_grows Mf M') by (unfold M', m_E; eapply mem_grows_trans; apply wbytes_grows).
      (* [comment removed for export] *)
      assert (WALL : forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ ctxV a \/ NB a \/ (A_ERRNO <= a < A_ERRNO + 4) \/ tailW a).
      { intros a Ha NE. destruct (decide (M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a))) as [E1|NE1].
        - rewrite E1 in NE. destruct (decide (Mf (Z_to_bv 64 a) = MT (Z_to_bv 64 a))) as [E3|NE3].
          + rewrite E3 in NE. destruct (TW a Ha NE) as [W|[W|[W|W]]]; [left; exact W | right; left; exact W | right; right; left; exact W | right; right; right; left; exact W].
          + right; right; right; right. exact (WT a Ha NE3).
        - right; right; right; right. unfold tailW. pose proof (WE a Ha NE1). (first [ (clear H0 HRX Hbrk' HeT; lia) | lia ]). }
      (* [comment removed for export] *)
      assert (RB : forall a v, cell Mf a 8 v -> 0 <= a -> a + 8 < 2 ^ 64 -> (a + 8 <= p + 24 \/ p + 40 <= a) -> cell M' a 8 v).
      { intros a v C Ha Ha8 D. unfold cell, M', m_E in *. do 2 rdn_peel1. exact C. }
      assert (EMf' : Mf = m_Ttail p sec (wbytes (m_T0 MT p acT) (Z_to_bv 64 (if s_areas st then ctx_meta_area_head else tl + 8)) (word_to_le_bytes 8 (Z_to_bv 64 p)))) by exact EMf.
      assert (HDR : (if s_areas st then ctx_meta_area_head else tl + 8) = ctx_meta_area_head \/
                    (s_areas st <> [] /\ (if s_areas st then ctx_meta_area_head else tl + 8) = tl + 8)).
      { destruct (s_areas st); [left; reflexivity | right; split; [discriminate | reflexivity]]. }
      assert (HD0 : 0 <= (if s_areas st then ctx_meta_area_head else tl + 8) /\ (if s_areas st then ctx_meta_area_head else tl + 8) + 8 < 2 ^ 64 /\
                    ((if s_areas st then ctx_meta_area_head else tl + 8) + 8 <= ctx_meta_area_tail \/
                     ((if s_areas st then ctx_meta_area_head else tl + 8) + 16 <= IMG_LO \/ IMG_HI <= (if s_areas st then ctx_meta_area_head else tl + 8))) /\
                    ((if s_areas st then ctx_meta_area_head else tl + 8) + 8 <= p \/ p + 4096 <= (if s_areas st then ctx_meta_area_head else tl + 8))).
      { destruct HDR as [E|[NE E]]; rewrite E; [unfold ctx_meta_area_head, ctx_meta_area_tail, CTX; (first [ (clear E WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ])|]. destruct (TL3a NE) as (A & Ai & [B|B]); unfold ctx_meta_area_tail, CTX; lia. }
      destruct HD0 as (HD1 & HD2 & HD3 & HD4).
      assert (Cac : cell M' ctx_avail_meta_area_count 8 (acT - 1)).
      { apply RB; [| unfold ctx_avail_meta_area_count, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_avail_meta_area_count, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_avail_meta_area_count, CTX; (first [ (clear HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ])].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        do 7 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Ccur : cell M' ctx_avail_meta_areas 8 (p + 4096)).
      { apply RB; [| unfold ctx_avail_meta_areas, CTX; lia | unfold ctx_avail_meta_areas, CTX; lia | unfold ctx_avail_meta_areas, CTX; lia].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        do 6 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Ctl : cell M' ctx_meta_area_tail 8 p).
      { apply RB; [| unfold ctx_meta_area_tail, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_meta_area_tail, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_meta_area_tail, CTX; (first [ (clear HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ])].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        do 4 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Cchk : cell M' p 8 sec).
      { apply RB; [| lia | lia | lia].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Cns : cell M' (p + 16) 4 NSLOTS).
      { unfold cell, M', m_E. do 2 rdn_peel1.
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX, NSLOTS in *.
        do 2 rdn_peel1. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 101))) as RH. rewrite length_N_to_le_bytes in RH. apply RH. zsimp; lia. }
      assert (Cam : cell M' ctx_avail_meta 8 (p + 64)).
      { apply RB; [| unfold ctx_avail_meta, CTX; lia | unfold ctx_avail_meta, CTX; lia | unfold ctx_avail_meta, CTX; lia].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia. }
      assert (Camc : cell M' ctx_avail_meta_count 8 100).
      { apply RB; [| unfold ctx_avail_meta_count, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_avail_meta_count, CTX; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_avail_meta_count, CTX; (first [ (clear HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ])].
        rewrite EMf'. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        apply rdn_wbytes_hit8. zsimp; lia. }
      (* [comment removed for export] *)
      assert (RBT : forall a v, cell MT a 8 v -> IMG_LO <= a -> a + 8 <= IMG_HI -> (forall y, a <= y < a + 8 -> ~ tailW y) -> cell M' a 8 v).
      { intros a v C Ha Ha8 OUT. eapply cell_agree; [lia | cbn; lia | | exact C]. intros y Hr Hy. cbn in Hy.
        destruct (decide (M' (Z_to_bv 64 y) = Mf (Z_to_bv 64 y))) as [E1|NE1].
        - rewrite E1. destruct (decide (Mf (Z_to_bv 64 y) = MT (Z_to_bv 64 y))) as [E3|NE3]; [exact E3|]. exfalso. exact (OUT y Hy (WT y Hr NE3)).
        - exfalso. pose proof (WE y Hr NE1). (first [ (clear HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]). }
      assert (Csh : cell M' ctx_meta_alloc_shift 8 sh').
      { apply RBT; [exact Tsh | unfold ctx_meta_alloc_shift, CTX; lia | unfold ctx_meta_alloc_shift, CTX; lia |].
        intros y Hy W. unfold tailW, ctx_meta_alloc_shift, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        destruct W as [W|[W|[[Z0 W]|[W|[[NE W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]); destruct (TL3 NE) as (? & ? & ?); lia. }
      assert (Ccb : cell M' ctx_brk 8 cb').
      { apply RBT; [exact Tcb | unfold ctx_brk, CTX; lia | unfold ctx_brk, CTX; lia |].
        intros y Hy W. unfold tailW, ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
        destruct W as [W|[W|[[Z0 W]|[W|[[NE W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]); destruct (TL3 NE) as (? & ? & ?); lia. }
      assert (Chd : cell M' ctx_meta_area_head 8 (head_of (UbMhAMetaN.areas' st p))).
      { unfold UbMhAMetaN.areas'. rewrite head_of_app. destruct HDR as [E|[NE E]].
        - (* [comment removed for export] *)
          assert (EA : s_areas st = []) by (destruct (s_areas st); [reflexivity | unfold ctx_meta_area_head, CTX in E; exfalso; destruct (TL3a ltac:(discriminate)) as (? & ? & ?); lia]).
          rewrite EA. apply RB; [| unfold ctx_meta_area_head, CTX; lia | unfold ctx_meta_area_head, CTX; lia | unfold ctx_meta_area_head, CTX; lia].
          rewrite EMf', E. unfold cell, m_Ttail, m_T0, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
          do 5 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
        - (* [comment removed for export] *)
          pose proof (rc_mah st M (rp_ctx st M HREP)) as C. rewrite (wc_head st (WF_ctx st L HWF)) in C.
          assert (CT : cell MT ctx_meta_area_head 8 (head_of (s_areas st))).
          { apply T_agree; [unfold ctx_meta_area_head, CTX; (first [ (clear HD4 HD3 HD2 HD1 E EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_meta_area_head, CTX, A_ERRNO, TPV; (first [ (clear HD4 HD3 HD2 HD1 E EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | unfold ctx_meta_area_head, CTX; cbn; (first [ (clear HD4 HD3 HD2 HD1 E EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT TW; lia) | lia ]) | ctx_out | exact C]. }
          destruct (TL3a NE) as (TL4 & TL4i & TL5). rewrite E in HD1, HD2, HD3, HD4.
          clear C. destruct (s_areas st) as [|a0 l0]; [exfalso; exact (NE eq_refl)|]. cbn [head_of] in CT |- *.
          apply RBT; [exact CT | unfold ctx_meta_area_head, CTX; lia | unfold ctx_meta_area_head, CTX; lia |].
          intros y Hy W. unfold tailW, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
          destruct W as [W|[W|[[Z0 W]|[W|[[_ W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]). }
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      set (errb := fun x : word => ((A_ERRNO <=? bv_unsigned x) && (bv_unsigned x <? A_ERRNO + 4))%bool).
      set (M1 := fun x : word => if errb x then M x else M' x).
      assert (M1out : forall a, 0 <= a < 2 ^ 64 -> ~ (A_ERRNO <= a < A_ERRNO + 4) -> M1 (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha OUT. unfold M1, errb. rewrite u_Z2bv by lia.
        destruct (A_ERRNO <=? a) eqn:E1; destruct (a <? A_ERRNO + 4) eqn:E2; cbn [andb]; try reflexivity.
        apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. exact (OUT (conj E1 E2)). }
      assert (M1in : forall a, 0 <= a < 2 ^ 64 -> A_ERRNO <= a < A_ERRNO + 4 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha IN. unfold M1, errb. rewrite u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      assert (M1cell : forall a k v, cell M' a k v -> 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= A_ERRNO \/ A_ERRNO + 4 <= a) -> cell M1 a k v).
      { intros a k v C Ha Hk D. eapply cell_agree; [exact Ha | exact Hk | | exact C]. intros y Hr Hy. apply (M1out y Hr). (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' RB TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg HeT; lia) | lia ]). }
      assert (CLOSE : WF stN L /\ REP stN M1).
      { apply (UbMhAMetaN.newarea_close st L M M1 HWF HREP Hfl Hac0 p regions' brk' (acT - 1) sh' cb'
                 Hp Hp_areas Hp_groups Hcnt HRgrp HRsub HRold HRnew ltac:(clear -TacR; lia) Hcur' Hsh' Hshacc' Hbrk' HWR' HWI').
        - (* [comment removed for export] *)
          intros a Hr Ha. destruct (decide (A_ERRNO <= a < A_ERRNO + 4)) as [IN|OUT]; [exact (M1in a Hr IN)|]. rewrite (M1out a Hr OUT).
          destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (WALL a Hr NE) as [W|[W|[W|[W|W]]]].
          + ceil; unfold AMSTK, CTX in *; lia.
          + unfold ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX in *; lia.
          + apply (NB_not_img a); [unfold CTX in *; lia | exact W].
          + exact (OUT W).
          + unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in *.
            destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear H0 HRX Hbrk' HeT; lia) | lia ]); destruct (TL3 NE2) as (? & ? & ?); lia.
        - (* [comment removed for export] *)
          intros a Hr [Ha NW]. rewrite (M1out a Hr) by (unfold CTX, A_ERRNO, TPV in *; lia).
          destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (WALL a Hr NE) as [W|[W|[W|[W|W]]]].
          + ceil; unfold AMSTK, CTX_END, CTX in *; lia.
          + apply NW. unfold UbMhAMetaN.ctxW. unfold ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, ctx_avail_meta, CTX in *. lia.
          + apply (NB_not_img a); [unfold CTX_END, CTX in *; lia | exact W].
          + unfold CTX, A_ERRNO, TPV in *; lia.
          + apply NW. unfold UbMhAMetaN.ctxW. unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, ctx_brk, CTX_END, CTX in *.
            destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]); destruct (TL3 NE2) as (? & ? & ?); lia.
        - apply (M1cell _ _ _ Cam); unfold ctx_avail_meta, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Camc); unfold ctx_avail_meta_count, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Cac); unfold ctx_avail_meta_area_count, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Csh); unfold ctx_meta_alloc_shift, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Chd); unfold ctx_meta_area_head, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Ctl); unfold ctx_meta_area_tail, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Ccur); unfold ctx_avail_meta_areas, CTX, A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Ccb); unfold ctx_brk, CTX, A_ERRNO, TPV; cbn; lia.
        - (* [comment removed for export] *) intros a Hd D. pose proof (dfoot_rng a Hd) as AR.
          destruct (decide (A_ERRNO <= a < A_ERRNO + 4)) as [IN|OUT]; [rewrite (M1in a AR IN); exact D|].
          rewrite (M1out a AR OUT). apply GE. apply GT. apply TKeep; [exact Hd | exact D].
        - (* [comment removed for export] *)
          intros ar a Har Ha Ntl. pose proof (wa_rng st (WF_areas st L HWF) ar Har) as (Aal & Alo & Ahi). ceil; unfold HEAPLO in Alo, Ahi.
          pose proof (area_img st L HWF ar Har) as AI.
          rewrite (M1out a) by (unfold A_ERRNO, TPV; clear -Alo Ahi Ha AI S1 S2; lia).
          destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (WALL a ltac:(lia) NE) as [W|[W|[W|[W|W]]]].
          + unfold AMSTK in *; lia.
          + unfold ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX in *; (first [ (clear AI Aal HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]).
          + destruct (NBfacts a W) as (_ & _ & NA & _). exact (NA ar Har Ha).
          + unfold A_ERRNO, TPV in *; (first [ (clear AI Aal HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]).
          + pose proof (Hp_areas ar Har) as D. unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in W.
            destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear M1cell HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]); try exact (Ntl W).
        - (* [comment removed for export] *)
          intros t a Ht Kt Ha. destruct (group_range st L HWF t Ht) as [G1 G2]. pose proof (Hp_maps t Ht Kt) as D.
          pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD. rewrite Kt in KD. destruct KD as (K1 & K2 & _).
          destruct (wr_rng st (WF_regions st L HWF) _ K2) as (Q1 & Q2 & _). cbn in Q1, Q2. ceil; unfold HEAPLO, g_map_end in *.
          pose proof (region_img st L HWF _ K2) as RI. cbn [rg_base rg_len] in RI.
          rewrite (M1out a) by (unfold A_ERRNO, TPV; clear -RI Ha Q1 Q2 G1 G2 S1 S2; lia).
          destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
          destruct (WALL a ltac:(lia) NE) as [W|[W|[W|[W|W]]]].
          + unfold AMSTK in *; lia.
          + unfold ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX in *; (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]).
          + destruct (NBfacts a W) as (_ & _ & _ & NG). apply (NG t Ht Kt). unfold g_map_end. lia.
          + unfold A_ERRNO, TPV in *; (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]).
          + unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in W.
            (* [comment removed for export] *)
            destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; [(first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]) | (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]) | (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]) | (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]) | | (first [ (clear RI HD3 HD2 HD1 HDR H0 HRX Hbrk' HeT; lia) | lia ]) | (first [ (clear RI HD3 HD2 HD1 HDR H0 HRX Hbrk' HeT; lia) | lia ]) | (first [ (clear RI D HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ]) | (first [ (clear RI HD3 HD2 HD1 HDR H0 HRX Hbrk' HeT; lia) | lia ])].
            destruct tl_cases as [[EA Etl]|(_ & Hin & _)]; [exact (NE2 Etl)|].
            destruct (area_apart_group st L HWF tl t Hin Ht). all: unfold gspan, g_span_end in *.
            * (* [comment removed for export] *) pose proof (gspan_gt st L HWF t Ht). unfold gspan, g_span_end in *.
              (* [comment removed for export] *)
              destruct (area_in_region st L HWF tl Hin) as (rr & Hrr & Hk & Z1 & Z2).
              assert (Hne : RG (g_mem st t) (4096 * g_maplen st t) (RGroup t) <> rr) by (intros <-; exact (Hk t eq_refl)).
              destruct (wr_disj st (WF_regions st L HWF) _ _ K2 Hrr Hne) as [DJ|DJ]; cbn in DJ; lia.
            * destruct (area_in_region st L HWF tl Hin) as (rr & Hrr & Hk & Z1 & Z2).
              assert (Hne : RG (g_mem st t) (4096 * g_maplen st t) (RGroup t) <> rr) by (intros <-; exact (Hk t eq_refl)).
              destruct (wr_disj st (WF_regions st L HWF) _ _ K2 Hrr Hne) as [DJ|DJ]; cbn in DJ; lia.
        - (* [comment removed for export] *) intros a Ha. rewrite (M1out a) by (unfold A_ERRNO, TPV; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ])). apply GE. apply GT. rewrite (TPage a Ha). discriminate.
        - apply (M1cell _ _ _ Cchk); unfold A_ERRNO, TPV; cbn; lia.
        - apply (M1cell _ _ _ Cns); unfold A_ERRNO, TPV; cbn; lia.
        - (* [comment removed for export] *)
          intros a Ha. rewrite (M1out a) by (unfold A_ERRNO, TPV; (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp HeT; lia) | lia ])).
          destruct (decide (p + 24 <= a < p + 40)) as [IN|OUT].
          + unfold M', m_E. destruct (decide (p + 24 + 8 <= a)) as [HI|LO].
            * rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). apply wbytes_z8_inside; lia.
            * apply wbytes_z8_inside; lia.
          + assert (E1 : M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a)).
            { destruct (decide (M' (Z_to_bv 64 a) = Mf (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso. pose proof (WE a ltac:(lia) NE). lia. }
            rewrite E1. assert (E3 : Mf (Z_to_bv 64 a) = MT (Z_to_bv 64 a)).
            { destruct (decide (Mf (Z_to_bv 64 a) = MT (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso. pose proof (WT a ltac:(lia) NE) as W.
              unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX in W.
              destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear H0 HRX Hbrk' HeT; lia) | lia ]); destruct (TL3 NE2) as (? & ? & ?); lia. }
            rewrite E3. apply TPage. lia. }
      destruct CLOSE as [WF1 REP1].
      assert (TE' : cell M' A_ERRNO 4 eT).
      { eapply cell_agree; [unfold A_ERRNO, TPV; lia | unfold A_ERRNO, TPV; cbn; lia | | exact TE]. intros y Hr Hy. cbn in Hy.
        destruct (decide (M' (Z_to_bv 64 y) = Mf (Z_to_bv 64 y))) as [E1|NE1].
        - rewrite E1. destruct (decide (Mf (Z_to_bv 64 y) = MT (Z_to_bv 64 y))) as [E3|NE3]; [exact E3|]. exfalso. pose proof (WT y Hr NE3) as W.
          unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX, A_ERRNO, TPV in *.
          destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear M1cell H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]); destruct (TL3 NE2) as (? & ? & ?); lia.
        - exfalso. pose proof (WE y Hr NE1). unfold A_ERRNO, TPV in *. (first [ (clear M1cell HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' NBreg HeT TW; lia) | lia ]). }
      assert (EW : errno_write M1 M' eT).
      { split; [exact TE'|]. intros x NE. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl) in NE.
        destruct (decide (A_ERRNO <= bv_unsigned x < A_ERRNO + 4)) as [IN|OUT].
        2:{ exfalso. apply NE. symmetry. exact (M1out _ XR OUT). }
        split; [exact IN|]. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl). rewrite (M1in _ XR IN) in NE.
        assert (E1 : M' (Z_to_bv 64 (bv_unsigned x)) = MT (Z_to_bv 64 (bv_unsigned x))).
        { destruct (decide (M' (Z_to_bv 64 (bv_unsigned x)) = Mf (Z_to_bv 64 (bv_unsigned x)))) as [E1|NE1].
          - rewrite E1. destruct (decide (Mf (Z_to_bv 64 (bv_unsigned x)) = MT (Z_to_bv 64 (bv_unsigned x)))) as [E3|NE3]; [exact E3|]. exfalso. pose proof (WT _ XR NE3) as W.
            unfold tailW, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta, ctx_avail_meta_count, CTX, A_ERRNO, TPV in *.
            destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]]; try (first [ (clear M1cell H0 HRX Hbrk' HeT TW; lia) | lia ]); destruct (TL3 NE2) as (? & ? & ?); lia.
          - exfalso. pose proof (WE _ XR NE1). unfold A_ERRNO, TPV in *. (first [ (clear M1cell HD3 HD2 HD1 HDR WALL H0 HRX Hbrk' HeT TW; lia) | lia ]). }
        rewrite E1 in NE |- *. exact (TED _ IN NE). }
      assert (WF' : WF (set_errno stN eT) L) by (apply WF_set_errno; [exact WF1 | pose proof (wc_errno st (WF_ctx st L HWF)); (first [ (clear M1cell HD4 HD3 HD2 HD1 HDR EMf' RB WALL TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp_groups Hp_areas Hp NBreg TW; lia) | lia ])]).
      pose proof (REP_set_errno stN L M1 M' eT WF1 REP1 EW) as REP'.
      exists (set_errno stN eT), M', mdlT, r', (p + 24).
      split; [reflexivity|].
      split; [exact WF'|]. split; [exact REP'|]. split; [apply (LEDGERX_same stN); [reflexivity | reflexivity | exact HLG']|].
      split; [exact Th|]. split; [exact Tlz|]. split; [exact Tmat|]. split; [exact Tfs|]. split; [exact Tfds|]. split; [exact Tlim|].
      split; [reflexivity|].
      split; [apply (proj2 (UbMhAMetaN.e_metaU st p regions' brk' (acT - 1) sh' cb' Hp (p + 24))); right; exists 0; split; [unfold NSLOTS; lia | unfold meta_addr, AREA_HDR, META_SZ; lia]|].
      split; [cbn [s_meta UbMhAMetaN.st']; replace (p + 24) with (meta_addr p 0) by (unfold meta_addr, AREA_HDR, META_SZ; lia); apply (UbMhAMetaN.n_meta_page st p Hp 0); unfold NSLOTS; lia|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [cbn [s_flist UbMhAMetaN.st']; rewrite Hfl; reflexivity|].
      split; [intros x Hx; cbn [s_meta UbMhAMetaN.st' set_errno]; apply (UbMhAMetaN.n_meta_grp st L HWF p Hp Hp_areas x Hx)|].
      split; [reflexivity|]. split; [cbn [s_errno set_errno]; exact HeT|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros x Hx; cbn [s_meta UbMhAMetaN.st']; apply (UbMhAMetaN.n_meta_old st L HWF p Hp Hp_areas x); exact (proj1 (wG_limbo st L (WF_groups st L HWF) x Hx))|].
      split.
      { intros IN. destruct (proj1 (wG_limbo st L (WF_groups st L HWF) _ IN)) as (ar & k & Har & Hk & Ek).
        destruct (Hp_areas ar Har); unfold meta_addr, AREA_HDR, META_SZ, NSLOTS in *; lia. }
      split; [intros x Ux; apply (proj2 (UbMhAMetaN.e_metaU st p regions' brk' (acT - 1) sh' cb' Hp x)); left; exact Ux|].
      split; [exact HRS|]. split; [exact HRL|]. split; [exact HRX|].
      split; [exact F10|]. split; [rewrite F2, H2; reflexivity|].
      split.
      { apply (keeps_final_am regs r' (bigT ++ ([10; 11; 12]%bv ++ clobE))).
        - eapply keeps_join; [exact KT|]. eapply keeps_join; [exact Kf | exact KE].
        - rewrite forallb_app, COVT. reflexivity.
        - exact F1. - rewrite F2, H2; reflexivity. - exact F8. - exact F9. - exact F18. - exact F19. - exact F20.
        - kept_rw KE. kept_rw Kf. exact T21. }
      split.
      { intros a Ha NE. destruct (WALL a Ha NE) as [W|[W|[W|[W|W]]]].
        - left. exact W.
        - right; left. unfold ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX_END, CTX in *. lia.
        - destruct (NBreg a W) as [Rg|Hol]; [right; right; left; exact Rg | right; right; right; right; exact Hol].
        - right; right; right; left. exact W.
        - unfold tailW in W. destruct W as [W|[W|[[Z0 W]|[W|[[NE2 W]|[W|[W|[W|W]]]]]]]].
          + right; left. unfold ctx_avail_meta_area_count, CTX_END, CTX in *. lia.
          + right; left. unfold ctx_avail_meta_areas, CTX_END, CTX in *. lia.
          + right; left. unfold ctx_meta_area_head, CTX_END, CTX in *. lia.
          + right; left. unfold ctx_meta_area_tail, CTX_END, CTX in *. lia.
          + right; right; left. destruct tl_cases as [[EA Etl]|(_ & Hin & _)]; [exfalso; exact (NE2 Etl)|].
            destruct (area_in_region st L HWF tl Hin) as (rr & Hrr & Hk & Z1 & Z2). destruct (HRsub rr Hrr) as (r2 & Hr2 & B1 & B2).
            exists r2. split; [exact Hr2|]. split; [|rewrite B1, B2; lia].
            intros x Kx. (* [comment removed for export] *)
            destruct r2 as [b2 l2 k2]. cbn in B1, B2, Kx. subst. apply HRgrp in Hr2.
            assert (Hne : RG (rg_base rr) (rg_len rr) (RGroup x) <> rr) by (intros E; apply (Hk x); rewrite <- E; reflexivity).
            destruct (wr_rng st (WF_regions st L HWF) rr Hrr) as (_ & _ & _ & LP & _).
            destruct (wr_disj st (WF_regions st L HWF) _ _ Hr2 Hrr Hne) as [DJ|DJ]; cbn in DJ; lia.
          + right; right; left. destruct HRnew as [(b2 & l2 & Hin & A1 & A2 & _)|(b2 & l2 & e2 & Hin & A1 & A2)].
            * exists (RG b2 l2 RBrk). cbn. repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]).
            * exists (RG b2 l2 (RMeta e2)). cbn. destruct (wr_meta stN HWR' b2 l2 e2 Hin) as (_ & E2 & _). repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]).
          + right; right; left. destruct HRnew as [(b2 & l2 & Hin & A1 & A2 & _)|(b2 & l2 & e2 & Hin & A1 & A2)].
            * exists (RG b2 l2 RBrk). cbn. repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]).
            * exists (RG b2 l2 (RMeta e2)). cbn. destruct (wr_meta stN HWR' b2 l2 e2 Hin) as (_ & E2 & _). repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]).
          + right; left. unfold ctx_avail_meta, CTX_END, CTX in *. lia.
          + right; right; left. destruct HRnew as [(b2 & l2 & Hin & A1 & A2 & _)|(b2 & l2 & e2 & Hin & A1 & A2)].
            * exists (RG b2 l2 RBrk). cbn. repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]).
            * exists (RG b2 l2 (RMeta e2)). cbn. destruct (wr_meta stN HWR' b2 l2 e2 Hin) as (_ & E2 & _). repeat split; try assumption; try (intros x E; discriminate E); try (first [ (clear HD4 HD3 HD2 HD1 HDR EMf' TL3 TL3a H0 EMf PI P0 Hp_maps HRX Hbrk' Hp HeT; lia) | lia ]). }
      eapply defined_grows; [|exact TDef]. eapply mem_grows_trans; [exact GT | exact GE].
    Qed.
  End Tail.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pru_4096 : page_round_up_Z 4096 = 4096. Proof using. repeat match reverse goal with PinX : _ |- _ => clear PinX end. reflexivity. Qed.





  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma region_free_shrink : forall l (a n a' n' : Z), 0 <= a -> 0 <= a' -> 0 <= n' -> a + n < 2 ^ 64 -> a <= a' -> a' + n' <= a + n ->
    region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true -> region_free l (Z_to_bv 64 a') (Z_to_bv 64 n') = true.
  Proof using X st. clear - X st.
    intros l a n a' n' Ha Ha' Hn' Han Hle1 Hle2 RF. apply region_free_intro. intros bb s Hin.
    pose proof (region_free_In _ _ _ _ _ RF Hin) as D. rewrite !u_Z2bv in D |- * by lia. lia.
  Qed.

End AMC.
End UbMhAMetaT.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct UbMhRsegs OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhBrkK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhAMetaW UbMhAMetaWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF.UbMhMmapW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapWF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS UbMhAMetaT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma errno_ret_ENOMEM : errno_ret ENOMEM = Z_to_bv 64 (2 ^ 64 - 12).
Proof. apply bv_eq. reflexivity. Qed.

Section AMC. (* [comment removed for export] *)
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (X : list (word * word)) (M : mem) (mdl : Model)
            (regs : bvmap 5 word) (rom : word -> option byte) (sp : Z).
  Variables (F : kfam) (bi : bool).
  Hypothesis HL : kfam_laws RSEGS F.
  Hypothesis HWF : WF st L.
  Hypothesis HREP : REP st M.
  Hypothesis HLG : LEDGERX st X (m_vmmaps mdl).
  Hypothesis XOK : xok X.
  Hypothesis Hh : m_halted mdl = None.
  Hypothesis Hlz : m_vm_lazy mdl = [].
  Hypothesis Hmat : m_vm_materialized mdl = [].
  Hypothesis HCNT : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Hypothesis HLEN : Z.of_nat (length X) + Z.of_nat (length (s_regions st)) <= 246.
  Hypothesis HBUD : XSUM X + RSUM (s_regions st) + 2 ^ 24 <= vm_limit (m_vmmaps mdl).
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 sp.
  Hypothesis Hra : ret_ok (getr regs 1).
  Hypothesis Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 TPV.
  Hypothesis DEF : defined M (sp - AMSTK) sp.
  Hypothesis Hok : forall c', am_post st L X sp regs M mdl rom c' -> kfx F bi c'.
  Hypothesis Hfail : forall c', am_fail st L X sp regs M mdl rom c' -> Kf F c'.

  #[local] Notation cx := (s_ctx st).
  #[local] Notation can := (UbMhAMetaS.can st).
  #[local] Notation M1 := (UbMhAMetaS.M1 st M regs sp).
  #[local] Notation ctxV := (UbMhAMetaT.ctxV).
  #[local] Notation kfx := (kfx F).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma am_fail_fst : forall regions' brk' cur' ac' sh' cb' (Mpre M' : mem) mdl' regs',
    let st1 := fst st regions' brk' cur' ac' sh' cb' in
    WF st1 L -> REP st1 Mpre -> LEDGERX st1 X (m_vmmaps mdl') -> errno_write Mpre M' 12 ->
    m_halted mdl' = None -> m_vm_lazy mdl' = [] -> m_vm_materialized mdl' = [] ->
    m_fs mdl' = m_fs mdl -> m_fds mdl' = m_fds mdl -> vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl) ->
    am_regions st st1 X ->
    getr regs' 10 = Z_to_bv 64 0 -> getr regs' 2 = getr regs 2 -> keeps_but AM_CLOB regs regs' ->
    (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> am_changed st1 sp a) ->
    defined M' (sp - AMSTK) sp ->
    am_fail st L X sp regs M mdl rom (mkCfg (mkst regs' (getr regs 1) M' rom) mdl').
  Proof using.
    intros regions' brk' cur' ac' sh' cb' Mpre M' mdl' regs' st1 W1 R1 LG1 EW X1 X2 X3 X4 X5 X6 AR A10 A2 KB FR DF.
    exists (set_errno st1 12), M', mdl', regs'.
    split; [reflexivity|].
    split; [apply WF_set_errno; [exact W1 | lia]|]. split; [exact (REP_set_errno st1 L Mpre M' 12 W1 R1 EW)|].
    split; [apply (LEDGERX_same st1); [reflexivity | reflexivity | exact LG1]|].
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [repeat (split; [reflexivity|]); intros x Ux; exact Ux|].
    split; [exact AR|].
    split; [exact A10|]. split; [exact A2|]. split; [exact KB|]. split; [|exact DF].
    intros a Ha NE. exact (FR a Ha NE).
  Qed.

  Lemma errno_write_intro : forall Mpre : mem,
    errno_write Mpre (wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) 12.
  Proof using X st.
    intros Mpre. split.
    - unfold cell, errno12. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 12)) Mpre (Z_to_bv 64 A_ERRNO)) as RH.
      rewrite length_N_to_le_bytes in RH. apply RH. unfold A_ERRNO, TPV. zsimp; lia.
    - intros a NE. pose proof (u64_range a) as AR. rewrite <- (Z_to_bv_u_eq' a (bv_unsigned a) eq_refl) in NE.
      pose proof (wbytes_diff_g Mpre A_ERRNO errno12 (bv_unsigned a) ltac:(unfold A_ERRNO, TPV; lia)
                    ltac:(unfold errno12, A_ERRNO, TPV; rewrite length_N_to_le_bytes; cbn; lia) ltac:(lia) NE) as IN.
      unfold errno12 in IN. rewrite length_N_to_le_bytes in IN.
      split; [lia|]. intros E0. rewrite (Z_to_bv_u_eq' a (bv_unsigned a) eq_refl) in NE.
      rewrite (wbytes_get_inside errno12 Mpre (Z_to_bv 64 A_ERRNO) a) in E0
        by (unfold errno12, A_ERRNO, TPV in *; wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      apply List.nth_error_None in E0. unfold errno12, A_ERRNO, TPV in *. rewrite length_N_to_le_bytes, u_Z2bv in E0 by lia. cbn in IN. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pru_4096 : page_round_up_Z 4096 = 4096. Proof using. reflexivity. Qed.
  Lemma Hsp' : CEIL + 144 <= sp /\ sp < 2 ^ 64. Proof using Hsp. unfold AMSTK in Hsp. exact Hsp. Qed.
  Lemma Hsp64 : CEIL + 64 <= sp /\ sp < 2 ^ 64. Proof using Hsp X st. unfold AMSTK in Hsp. lia. Qed.
  Lemma errno_sok : forall Mx : mem, store_ok RSEGS Mx (Z_to_bv 64 A_ERRNO) 4%nat = true.
  Proof using. intros Mx. apply store_ok_wseg. vm_compute. reflexivity. Qed.
  Lemma ctx_sok : forall Mx : mem, store_ok RSEGS Mx (Z_to_bv 64 CTX) 928%nat = true.
  Proof using. intros Mx. apply store_ok_wseg. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma cell_keep : forall (Mx : mem) (W : Z -> Prop) a k v,
    (forall y, 0 <= y < 2 ^ 64 -> Mx (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> (y < IMG_LO \/ IMG_HI <= y) \/ W y) ->
    cell M a k v -> IMG_LO <= a -> a + Z.of_nat k <= IMG_HI -> (forall y, a <= y < a + Z.of_nat k -> ~ W y) -> cell Mx a k v.
  Proof using X st.
    intros Mx W a k v HW C Ha Hk OUT. eapply cell_agree; [lia | lia | | exact C].
    intros y Hr Hy. destruct (decide (Mx (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
    destruct (HW y Hr NE) as [A|A]; [lia | exact (OUT y Hy A)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmMM.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    Hypothesis Hac : c_area_cnt cx = 0.
    #[local] Notation sh := (c_shift (s_ctx st)).
    #[local] Notation N := (UbMhAMetaR.c4_N st).
    Variables (rM : bvmap 5 word) (Mm : mem) (bigM : list reg).
    Hypothesis R2 : getr rM 2 = Z_to_bv 64 (sp - 64).
    Hypothesis R10 : getr rM 10 = Z_to_bv 64 0.
    Hypothesis R11 : getr rM 11 = Z_to_bv 64 N.
    Hypothesis R12 : getr rM 12 = Z_to_bv 64 0.
    Hypothesis R13 : getr rM 13 = Z_to_bv 64 34.
    Hypothesis R14 : getr rM 14 = Z_to_bv 64 (-1).
    Hypothesis R15 : getr rM 15 = Z_to_bv 64 0.
    Hypothesis R9 : getr rM 9 = Z_to_bv 64 (2 * 2 ^ sh).
    Hypothesis R20 : getr rM 20 = Z_to_bv 64 (2 ^ 64 - 1).
    Hypothesis R1 : getr rM 1 = Z_to_bv 64 0x66e4c.
    Hypothesis R19 : getr rM 19 = Z_to_bv 64 MLOCK.
    Hypothesis R8 : getr rM 8 = Z_to_bv 64 4096.
    Hypothesis R18 : getr rM 18 = Z_to_bv 64 A_CANARY.
    Hypothesis R21 : getr rM 21 = getr regs 21.
    Hypothesis R4 : getr rM 4 = Z_to_bv 64 TPV.
    Hypothesis KM : keeps_but bigM regs rM.
    Hypothesis COVM : forallb (fun r => existsb (fun x => bv_eqb x r) AM_CLOB || existsb (fun x => bv_eqb x r) AM_SAVED)%bool bigM = true.
    Hypothesis MmW : forall a, 0 <= a < 2 ^ 64 -> Mm (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - 56 <= a < sp) \/ (ctx_brk <= a < ctx_brk + 8).
    Hypothesis MmB : cell Mm ctx_brk 8 (2 ^ 64 - 1).
    Hypothesis MmG : mem_grows M Mm.
    Hypothesis MmS : forall a n bs, sp - 56 <= a -> a + Z.of_nat n <= sp -> rdn RSEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn RSEGS Mm (Z_to_bv 64 a) n = Some bs.
    Hypothesis MmD : defined Mm (sp - AMSTK) sp.

    (* [comment removed for export] *)
    #[local] Notation dst := (d_st st true).

    Lemma arm_MM : forall b, kfx b (mkCfg (mkst rM (0x682e8%bv : word) Mm rom) mdl).
    Proof using MmD MmS MmG MmB MmW COVM KM R4 R21 R18 R8 R19 R1 R20 R9 R15 R14 R13 R12 R11 R10 R2 bigM Hac Hac0 Hfl Hfail Hok DEF Hsp Hra H2 HBUD HLEN HCNT Hmat Hlz Hh XOK HLG HREP HWF HL bi sp regs M X L st RN.
      intros b.
      pose proof Hsp' as [S1 S2]. ceil.
      pose proof (HCNT Hfl Hac0) as Hcnt.
      pose proof (UbMhAMetaR.c4_N_rng st L HWF Hcnt Hac 0) as (N1 & N2 & N3). pose proof (UbMhAMetaR.c4_sh_rng st L HWF Hcnt Hac 0) as [SH1 SH2].
      assert (EN : N = 2 * 2 ^ sh * 4096) by (rewrite N3; lia).
      pose proof (UbMhAMetaS.can_rng st L HWF) as CANR.
      (* [comment removed for export] *)
      assert (SOK64 : store_ok RSEGS Mm (Z_to_bv 64 (sp - 64 - 64)) 64%nat = true).
      { eapply store_ok_defined; [exact MmD | unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia]. }
      destruct (mmW1_34 Mm (sp - 64) 0 N 0 34 ltac:(lia) SOK64 ltac:(lia) rM rom eq_refl R2 R10 R11 R12 R13 R14 R15)
        as (rN & RUN1 & Q2 & Q17 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & KN).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
      set (Mm2 := mm_frame Mm (sp - 64) (getr rM 1) (getr rM 8) (getr rM 9) (getr rM 18) (getr rM 19) (getr rM 20) (getr rM 21)).
      assert (Mm2W : forall x, 0 <= x < 2 ^ 64 -> Mm2 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - 128 <= x < sp) \/ (ctx_brk <= x < ctx_brk + 8)).
      { intros x Hx NE. unfold Mm2, mm_frame in NE.
        destruct (decide (Mm (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
        - rewrite <- E4 in NE. left. wdiff NE Mm x.
        - destruct (MmW x Hx NE4); [left; lia | right; assumption]. }
      assert (Mm2G : mem_grows M Mm2) by (unfold Mm2, mm_frame; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact MmG).
      assert (STK2 : forall d v (Mx : mem), 8 <= d <= 56 -> (forall y, sp - 128 <= y < sp - 64 -> Mx (Z_to_bv 64 y) = Mm2 (Z_to_bv 64 y)) ->
                     rdn RSEGS Mm2 (Z_to_bv 64 (sp - 64 - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                     rdn RSEGS Mx (Z_to_bv 64 (sp - 64 - d)) 8%nat = Some (word_to_le_bytes 8 v)).
      { intros d v Mx Hd AG R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
        intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as Xr. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl). apply AG. lia. }
      (* [comment removed for export] *)
      assert (PR : page_round_up_Z N = N) by (apply page_round_up_Z_aligned; first [lia | exact N2]).
      destruct (ledgerx_grant_na st L X mdl HWF HLG XOK N ltac:(lia) HLEN) as (a0 & GR0 & _).
      apply (kfx_mmap_na RSEGS F HL bi b rN (0x683ac%bv : word) Mm2 rom mdl W_68358 N Hh Hlz F_68358 E_68358 Q17 Q11 ltac:(lia) Q12 Q13 Q14 Q15);
        rewrite ?PR; [exists a0; exact GR0 | |].
      { (* [comment removed for export] *)
        unfold mmna_fail. rewrite errno_ret_ENOMEM. replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
        assert (SOK16 : store_ok RSEGS Mm2 (Z_to_bv 64 (sp - 64 - 80)) 16%nat = true).
        { eapply (store_ok_defined Mm2 (sp - AMSTK) sp); [| unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia].
          eapply defined_grows; [exact Mm2G | exact DEF]. }
        destruct (mmW2f Mm2 (sp - 64) 0 ltac:(unfold A_ERRNO, TPV; lia) SOK16 (errno_sok Mm2) ltac:(lia)
                    (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr rM 1) (getr rM 8) (getr rM 9) (getr rM 18) (getr rM 19) (getr rM 20) (getr rM 21)
                    ltac:(rewrite R1; apply ret_ok_even; reflexivity)
                    ltac:(gres; exact Q2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact Q16)
                    ltac:(gres; kept_rw KN; exact R4)
                    (STK2 8 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 16 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 24 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 32 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 40 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 48 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve))
                    (STK2 56 _ Mm2 ltac:(lia) ltac:(intros; reflexivity) ltac:(unfold Mm2, mm_frame; rdn_solve)))
          as (rF & RUNF & F2 & F10 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & KF).
        eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNF |].
        set (Mf := mm_ffail Mm2 (sp - 64) (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8)).
        assert (MfW : forall x, 0 <= x < 2 ^ 64 -> Mf (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                      (sp - 144 <= x < sp) \/ (ctx_brk <= x < ctx_brk + 8) \/ (A_ERRNO <= x < A_ERRNO + 4)).
        { intros x Hx NE. unfold Mf, mm_ffail, errno12 in NE.
          destruct (decide (Mm2 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite <- E4 in NE. unfold A_ERRNO, TPV in *. wdiff NE Mm2 x.
          - destruct (Mm2W x Hx NE4); [left; lia | right; left; assumption]. }
        assert (MfG : mem_grows M Mf) by (unfold Mf, mm_ffail; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [exact Mm2G | exact MmG]).
        assert (AGf : forall a k v, cell M a k v -> IMG_LO <= a -> a + Z.of_nat k <= IMG_HI ->
                       (forall y, a <= y < a + Z.of_nat k -> ~ ((ctx_brk <= y < ctx_brk + 8) \/ (A_ERRNO <= y < A_ERRNO + 4))) -> cell Mf a k v).
        { intros a k v C Ha Hk OUT. apply (cell_keep Mf (fun y => (ctx_brk <= y < ctx_brk + 8) \/ (A_ERRNO <= y < A_ERRNO + 4)) a k v).
          2: exact C. 2: exact Ha. 2: exact Hk. 2: exact OUT.
          intros y Hy NE. destruct (MfW y Hy NE) as [A|A]; [left; right; ceil; lia | right; exact A]. }
        assert (STKf : forall d v, 8 <= d <= 56 -> rdn RSEGS M1 (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                       rdn RSEGS Mf (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v)).
        { intros d v Hd R. rewrite <- (MmS (sp - d) 8%nat _ ltac:(lia) ltac:(cbn; lia) R). symmetry. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
          unfold Mf, mm_ffail, errno12, Mm2, mm_frame, A_ERRNO, TPV. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity. }
        rewrite R1.
        destruct (amM2f Mf sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) Hsp64 Hra
                    ltac:(pose proof (rc_canary st M (rp_statics st M HREP)) as C; unfold cell in C; apply (AGf _ _ _ C); unfold A_CANARY, ctx_brk, CTX, A_ERRNO, TPV; cbn; intros; lia)
                    (STKf 56 _ ltac:(lia) (UbMhAMetaS.M1_can st X M regs sp Hsp)) (STKf 8 _ ltac:(lia) (UbMhAMetaS.M1_ra st X M regs sp Hsp))
                    (STKf 16 _ ltac:(lia) (UbMhAMetaS.M1_s0 st X M regs sp Hsp)) (STKf 24 _ ltac:(lia) (UbMhAMetaS.M1_s1 st X M regs sp Hsp))
                    (STKf 32 _ ltac:(lia) (UbMhAMetaS.M1_s2 st X M regs sp Hsp)) (STKf 40 _ ltac:(lia) (UbMhAMetaS.M1_s3 st X M regs sp Hsp))
                    (STKf 48 _ ltac:(lia) (UbMhAMetaS.M1_s4 st X M regs sp Hsp))
                    rF rom F2 ltac:(rewrite F18; exact R18) F10 ltac:(rewrite F20; exact R20))
          as (rZ & RUNZ & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & KZ).
        replace (Z_to_bv 64 421452) with (421452%bv : word) by (apply bv_eq; reflexivity).
        eapply (kf_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNZ |].
        apply Hfail.
        (* [comment removed for export] *)
        set (Mpre := wbytes (wbytes Mm2 (Z_to_bv 64 (sp - 64 - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x683d0)))
                            (Z_to_bv 64 (sp - 64 - 80)) (word_to_le_bytes 8 (getr (regupd rN 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
        assert (EMf : Mf = wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
        assert (MpreW : forall x, 0 <= x < 2 ^ 64 -> Mpre (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - 144 <= x < sp) \/ (ctx_brk <= x < ctx_brk + 8)).
        { intros x Hx NE. unfold Mpre in NE.
          destruct (decide (Mm2 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite <- E4 in NE. left. wdiff NE Mm2 x.
          - destruct (Mm2W x Hx NE4); [left; lia | right; assumption]. }
        assert (MpreG : mem_grows M Mpre) by (unfold Mpre; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); first [exact Mm2G | exact MmG]).
        rewrite EMf.
        apply (am_fail_fst (s_regions st) (d_brk st true) (c_cursor cx) (c_area_cnt cx) sh (d_cb st true) Mpre _ mdl rZ).
        - exact (d_WF st L HWF true).
        - apply (f_REP st L M Mpre HWF HREP (s_regions st) (d_brk st true) (c_cursor cx) (c_area_cnt cx) sh (d_cb st true));
            [exact (d_Hac' st L HWF) | exact (d_Hsh' st L HWF) | ..].
          + intros a Hr Ha. destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a Hr NE); ceil; unfold ctx_brk, CTX in *; lia.
          + intros a Hr [Ha NW]. destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a Hr NE) as [W|W]; [ceil; unfold CTX_END, CTX in *; lia|]. apply NW. unfold fctxW. right; right. exact W.
          + apply (cell_keep Mpre (fun y => ctx_brk <= y < ctx_brk + 8)); [intros y Hy NE; destruct (MpreW y Hy NE); [left; right; ceil; lia | right; assumption] | exact (rc_amac st M (rp_ctx st M HREP)) | | |];
              unfold ctx_avail_meta_area_count, ctx_brk, CTX; cbn; intros; lia.
          + apply (cell_keep Mpre (fun y => ctx_brk <= y < ctx_brk + 8)); [intros y Hy NE; destruct (MpreW y Hy NE); [left; right; ceil; lia | right; assumption] | exact (rc_mas st M (rp_ctx st M HREP)) | | |];
              unfold ctx_meta_alloc_shift, ctx_brk, CTX; cbn; intros; lia.
          + apply (cell_keep Mpre (fun y => ctx_brk <= y < ctx_brk + 8)); [intros y Hy NE; destruct (MpreW y Hy NE); [left; right; ceil; lia | right; assumption] | exact (rc_amas st M (rp_ctx st M HREP)) | | |];
              unfold ctx_avail_meta_areas, ctx_brk, CTX; cbn; intros; lia.
          + unfold d_cb. unfold cell, Mpre, Mm2, mm_frame, ctx_brk, CTX in *. do 9 rdn_peel1. exact MmB.
          + intros a Hd D. apply MpreG. exact D.
          + intros ar a Har Ha. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Aal & Alo & Ahi).
            destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a ltac:(ceil; unfold HEAPLO in *; lia) NE); [ceil; lia | unfold ctx_brk, CTX in *; lia].
          + intros t a Ht Kt Ha. destruct (group_range st L HWF t Ht) as [G1 G2].
            pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD. rewrite Kt in KD. destruct KD as (K1 & K2 & _).
            destruct (wr_rng st (WF_regions st L HWF) _ K2) as (W1 & W2 & _). cbn in W1, W2. pose proof (region_img st L HWF _ K2) as RI. cbn [rg_base rg_len] in RI.
            unfold g_map_end in Ha.
            destruct (decide (Mpre (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a ltac:(ceil; unfold HEAPLO in *; lia) NE); [ceil; lia | unfold ctx_brk, CTX in *; lia].
        - apply (d_ledger st X (m_vmmaps mdl) HLG true); try reflexivity. intros E; discriminate E.
        - apply errno_write_intro.
        - exact Hh. - exact Hlz. - exact Hmat. - reflexivity. - reflexivity. - reflexivity.
        - split; [cbn [s_regions fst]; lia|]. split; [cbn [s_regions fst]; lia|]. cbn [s_regions fst]. intros r Hr. left. exists r. split; [exact Hr | split; reflexivity].
        - exact Z10.
        - rewrite Z2, H2. reflexivity.
        - apply (UbMhAMetaS.keeps_final_am regs rZ (bigM ++ (clobMM1 ++ ([10]%bv ++ ([1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%bv ++ clobZ))))).
          + eapply UbMhAMetaS.keeps_join; [exact KM|]. eapply UbMhAMetaS.keeps_join; [exact KN|].
            eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
            eapply UbMhAMetaS.keeps_join; [exact KF | exact KZ].
          + rewrite forallb_app, COVM. reflexivity.
          + exact Z1. + rewrite Z2, H2; reflexivity. + exact Z8. + exact Z9. + exact Z18. + exact Z19. + exact Z20.
          + kept_rw KZ. rewrite F21. exact R21.
        - intros a Ha NE. rewrite <- EMf in NE. destruct (MfW a Ha NE) as [W|[W|W]].
          + left. unfold AMSTK. exact W.
          + right; left. unfold ctx_brk, CTX_END, CTX in *. lia.
          + right; right; left. exact W.
        - rewrite <- EMf. eapply defined_grows; [exact MfG | exact DEF]. }
      (* [comment removed for export] *)
      intros a GR. unfold mmna_grant. rewrite PR.
      replace (v_addi (0x683ac%bv : word) 4) with (0x683b0%bv : word) by (apply bv_eq; reflexivity).
      pose proof GR as GR'. unfold grant_ok_na_pin in GR'. rewrite !Bool.andb_true_iff in GR'. destruct GR' as [[[GA1 GA2] GA3] GA4].
      apply Z.eqb_eq in GA1. apply Z.ltb_lt in GA2. apply Z.leb_le in GA3. unfold page_size in GA1.
      pose proof (grant_range_hz (m_vmmaps mdl) _ a (Z_to_bv 64 N) (lx_top st X _ HLG) ltac:(rewrite <- (lx_res st X _ HLG); exact GA4)
                    ltac:(rewrite u_Z2bv by lia; lia) GA1 ltac:(rewrite u_Z2bv by lia; exact N2) ltac:(rewrite u_Z2bv by lia; exact GA3)) as [HZ HI].
      rewrite u_Z2bv in HZ, HI by lia.
      set (p0 := bv_unsigned a) in *.
      assert (Ea : a = Z_to_bv 64 p0) by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
      assert (HLO : 4096 <= p0).
      { clear -GA1 GA2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
      assert (HP0 : p0 mod 4096 = 0 /\ HEAPLO <= p0 /\ p0 + N <= CEIL) by (unfold HEAPLO; lia).
      assert (HRF : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) (Z_to_bv 64 p0) (Z_to_bv 64 N) = true) by (rewrite <- Ea; exact GA4).
      pose proof (UbMhAMetaR.c4_apart st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF) as [AP APX].
      rewrite Ea. set (Mm3 := unfill (Z_to_bv 64 p0) (Z_to_bv 64 N) Mm2).
      set (mdl1 := noaccess_model (Z_to_bv 64 p0) (Z_to_bv 64 N) mdl).
      pose (h1 := mkVmMapsFull (vm_reserved (m_vmmaps mdl)) ((Z_to_bv 64 p0, Z_to_bv 64 N) :: vm_maps (m_vmmaps mdl)) ((Z_to_bv 64 p0, Z_to_bv 64 N) :: vm_noaccess (m_vmmaps mdl))
                 (vm_start_brk (m_vmmaps mdl)) (vm_brk (m_vmmaps mdl)) (vm_limit (m_vmmaps mdl)) (vm_mmap_base (m_vmmaps mdl)) (vm_init_sp (m_vmmaps mdl))).
      pose proof (with_vmmaps_facts h1 mdl) as MF. change (with_vmmaps h1 mdl) with mdl1 in MF. destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
      (* [comment removed for export] *)
      assert (Mm3out : forall y, 0 <= y < 2 ^ 64 -> ~ (p0 <= y < p0 + N) -> Mm3 (Z_to_bv 64 y) = Mm2 (Z_to_bv 64 y)).
      { intros y Hy OUT. unfold Mm3. apply unfill_outZ; lia. }
      destruct (mmW2 (sp - 64) 0 ltac:(lia) ltac:(lia) (regupd rN 10 (Z_to_bv 64 p0)) rom Mm3 p0
                  (getr rM 1) (getr rM 8) (getr rM 9) (getr rM 18) (getr rM 19) (getr rM 20) (getr rM 21)
                  ltac:(lia) ltac:(right; lia) ltac:(rewrite R1; apply ret_ok_even; reflexivity)
                  ltac:(gres; exact Q2) ltac:(gres; reflexivity) ltac:(gres; exact Q16)
                  (STK2 8 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 16 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 24 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 32 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 40 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 48 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve))
                  (STK2 56 _ Mm3 ltac:(lia) ltac:(intros; apply Mm3out; lia) ltac:(unfold Mm2, mm_frame; rdn_solve)))
        as (rP & RUN3 & P2 & P10 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
      eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN3 |].
      rewrite R1. replace (Z_to_bv 64 421452) with (421452%bv : word) by (apply bv_eq; reflexivity).
      (* [comment removed for export] *)
      assert (Mm3W : forall x, 0 <= x < 2 ^ 64 -> Mm3 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - 128 <= x < sp) \/ (ctx_brk <= x < ctx_brk + 8) \/ (p0 <= x < p0 + N)).
      { intros x Hx NE. destruct (decide (p0 <= x < p0 + N)) as [IN|OUT]; [right; right; exact IN|].
        rewrite (Mm3out x Hx OUT) in NE. destruct (Mm2W x Hx NE); [left; assumption | right; left; assumption]. }
      assert (AG3 : forall a1 k v, cell M a1 k v -> IMG_LO <= a1 -> a1 + Z.of_nat k <= IMG_HI ->
                     (forall y, a1 <= y < a1 + Z.of_nat k -> ~ (ctx_brk <= y < ctx_brk + 8)) -> cell Mm3 a1 k v).
      { intros a1 k v C Ha Hk OUT. apply (cell_keep Mm3 (fun y => ctx_brk <= y < ctx_brk + 8) a1 k v); [| exact C | exact Ha | exact Hk | exact OUT].
        intros y Hy NE. destruct (Mm3W y Hy NE) as [A|[A|A]]; [left; right; ceil; lia | right; exact A | left; clear -A HI; lia]. }
      assert (SH3 : rdn RSEGS Mm3 (Z_to_bv 64 ctx_meta_alloc_shift) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 sh))).
      { apply (AG3 _ _ _ (rc_mas st M (rp_ctx st M HREP))); unfold ctx_meta_alloc_shift, ctx_brk, CTX; cbn; intros; lia. }
      destruct (amM2 rP rom Mm3 sh p0 ltac:(lia) ltac:(unfold HEAPLO; lia) ltac:(lia) ltac:(lia)
                  ltac:(rewrite P19; exact R19) ltac:(rewrite P8; exact R8) P10 ltac:(rewrite P9; exact R9) ltac:(rewrite P20; exact R20) SH3 (ctx_sok Mm3))
        as (rQ & RUN4 & U10 & U11 & U12 & U9 & U1 & KQ).
      eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN4 |].
      set (Mm4 := wbytes (wbytes (wbytes Mm3 (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 (2 * 2 ^ sh - 1))))
                    (Z_to_bv 64 ctx_meta_alloc_shift) (word_to_le_bytes 8 (Z_to_bv 64 (sh + 1)))) (Z_to_bv 64 ctx_avail_meta_areas) (word_to_le_bytes 8 (Z_to_bv 64 (p0 + 4096)))).
      assert (Mm4W : forall x, 0 <= x < 2 ^ 64 -> Mm4 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                    (sp - 128 <= x < sp) \/ ((ctx_brk <= x < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= x < ctx_avail_meta_area_count + 16) \/
                                             (ctx_avail_meta_areas <= x < ctx_avail_meta_areas + 8)) \/ (p0 <= x < p0 + N)).
      { intros x Hx NE. unfold Mm4 in NE.
        destruct (decide (Mm3 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
        - rewrite <- E4 in NE. right; left. unfold ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, ctx_brk, CTX in *. wdiff NE Mm3 x.
        - destruct (Mm3W x Hx NE4) as [W|[W|W]]; [left; exact W | right; left; left; exact W | right; right; exact W]. }
      (* [comment removed for export] *)
      assert (D4 : defined Mm4 (sp - AMSTK) sp).
      { intros y Hy. unfold AMSTK in Hy. unfold Mm4. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). rewrite (Mm3out y) by lia.
        unfold Mm2, mm_frame. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). apply MmD. unfold AMSTK. lia. }
      assert (SOK16 : store_ok RSEGS Mm4 (Z_to_bv 64 (sp - 64 - 16)) 16%nat = true).
      { eapply (store_ok_defined Mm4 (sp - AMSTK) sp); [exact D4 | unfold AMSTK; lia | cbn; lia | unfold AMSTK; lia | lia]. }
      assert (AG4 : forall a1 k v, cell M a1 k v -> IMG_LO <= a1 -> a1 + Z.of_nat k <= IMG_HI ->
                     (forall y, a1 <= y < a1 + Z.of_nat k -> ~ ((ctx_brk <= y < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= y < ctx_avail_meta_area_count + 16) \/
                                                             (ctx_avail_meta_areas <= y < ctx_avail_meta_areas + 8))) -> cell Mm4 a1 k v).
      { intros a1 k v C Ha Hk OUT. eapply (cell_keep Mm4 _ a1 k v); [| exact C | exact Ha | exact Hk | exact OUT].
        intros y Hy NE. destruct (Mm4W y Hy NE) as [A|[A|A]]; [left; right; ceil; lia | right; exact A | left; clear -A HI; lia]. }
      assert (PG4 : rdn RSEGS Mm4 (Z_to_bv 64 A_PAGESIZE) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096))).
      { apply (AG4 _ _ _ (rc_pagesize st M (rp_statics st M HREP))); unfold A_PAGESIZE, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX; cbn; intros; lia. }
      assert (AL4 : (p0 + 4096) mod 4096 = 0) by (rewrite Z.add_mod, GA1 by lia; reflexivity).
      destruct (mpW1 Mm4 (sp - 64) (p0 + 4096) 3 ltac:(lia) SOK16 ltac:(split; [lia|]; split; [lia | exact AL4]) PG4 rQ rom
                  ltac:(kept_rw KQ; exact P2) U10 U11 U12) as (rS & RUN5 & V2 & V17 & V10 & V11 & V12 & KS).
      eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN5 |].
      (* [comment removed for export] *)
      set (Mm5 := mp_frame Mm4 (sp - 64) (getr rQ 1)).
      assert (Mm5W : forall x, 0 <= x < 2 ^ 64 -> Mm5 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                    (sp - 128 <= x < sp) \/ ((ctx_brk <= x < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= x < ctx_avail_meta_area_count + 16) \/
                                             (ctx_avail_meta_areas <= x < ctx_avail_meta_areas + 8)) \/ (p0 <= x < p0 + N)).
      { intros x Hx NE. unfold Mm5, mp_frame in NE.
        destruct (decide (Mm4 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
        - rewrite <- E4 in NE. left. wdiff NE Mm4 x.
        - exact (Mm4W x Hx NE4). }
      apply (kfx_mprotect RSEGS F HL bi bi rS (0x68404%bv : word) Mm5 rom mdl1 W_683b0 (Z_to_bv 64 (p0 + 4096)) 4096
               ltac:(rewrite MF2; exact Hh) ltac:(rewrite MF3; exact Hlz) F_683b0 E_683b0 V17 V10
               ltac:(unfold page_size; rewrite u_Z2bv by lia; exact AL4) V11 ltac:(lia)
               ltac:(rewrite pru_4096, u_Z2bv by lia; unfold two_pow_64; lia) V12).
      { rewrite pru_4096, MF1. unfold h1. cbn [vm_noaccess]. apply map_contains_head; rewrite !u_Z2bv by lia; lia. }
      { rewrite pru_4096, MF1. unfold h1. cbn [vm_maps]. apply map_contains_head; rewrite !u_Z2bv by lia; lia. }
      { apply mprotect_budget_ok_intro; [rewrite MF3; exact Hlz | rewrite MF4; exact Hmat |].
        rewrite MF1. unfold h1. unfold vm_live_bytes. cbn [vm_maps vm_limit]. rewrite live_bytes_cons, u_Z2bv by lia.
        pose proof (live_bytes_ledgerx st L HWF X _ HLG) as LB. unfold vm_live_bytes in LB. rewrite LB. rewrite ?pru_4096, ?u_Z2bv by lia. lia. }
      { (* [comment removed for export] *)
        unfold mpr_fail. rewrite errno_ret_ENOMEM. replace (v_addi (0x68404%bv : word) 4) with (0x68408%bv : word) by (apply bv_eq; reflexivity).
        assert (SOK16f : store_ok RSEGS Mm5 (Z_to_bv 64 (sp - 64 - 32)) 16%nat = true).
        { eapply (store_ok_defined Mm5 (sp - AMSTK) sp); [| unfold AMSTK; lia | unfold AMSTK; cbn; lia | unfold AMSTK; lia | lia].
          unfold Mm5, mp_frame. apply defined_wbytes. exact D4. }
        destruct (mpW2f Mm5 (sp - 64) ltac:(unfold A_ERRNO, TPV; lia) SOK16f (errno_sok Mm5) (regupd rS 10 (Z_to_bv 64 (2 ^ 64 - 12))) rom (getr rQ 1)
                    ltac:(rewrite U1; apply ret_ok_even; reflexivity) ltac:(gres; exact V2) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                    ltac:(gres; kept_rw KS; kept_rw KQ; kept_rw KP; gres; kept_rw KN; exact R4)
                    ltac:(unfold Mm5, mp_frame; apply rdn_wbytes_hit8; zsimp; lia))
          as (rF & RUNF & F2 & F10 & F1 & F8 & KF).
        eapply (kf_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUNF |].
        rewrite U1.
        set (Mf := mp_ffail Mm5 (sp - 64) (getr (regupd rS 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8)).
        set (Mpre := wbytes (wbytes Mm5 (Z_to_bv 64 (sp - 64 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x6840c)))
                            (Z_to_bv 64 (sp - 64 - 32)) (word_to_le_bytes 8 (getr (regupd rS 10 (Z_to_bv 64 (2 ^ 64 - 12))) 8))).
        assert (EMf : Mf = wbytes Mpre (Z_to_bv 64 A_ERRNO) errno12) by reflexivity.
        assert (MpreW : forall x, 0 <= x < 2 ^ 64 -> Mpre (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                    (sp - 144 <= x < sp) \/ ((ctx_brk <= x < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= x < ctx_avail_meta_area_count + 16) \/
                                             (ctx_avail_meta_areas <= x < ctx_avail_meta_areas + 8)) \/ (p0 <= x < p0 + N)).
        { intros x Hx NE. unfold Mpre in NE.
          destruct (decide (Mm5 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite <- E4 in NE. left. wdiff NE Mm5 x.
          - destruct (Mm5W x Hx NE4) as [W|[W|W]]; [left; lia | right; left; exact W | right; right; exact W]. }
        assert (MfW : forall x, 0 <= x < 2 ^ 64 -> Mf (Z_to_bv 64 x) <> M (Z_to_bv 64 x) ->
                    (sp - 144 <= x < sp) \/ ((ctx_brk <= x < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= x < ctx_avail_meta_area_count + 16) \/
                                             (ctx_avail_meta_areas <= x < ctx_avail_meta_areas + 8)) \/ (p0 <= x < p0 + N) \/ (A_ERRNO <= x < A_ERRNO + 4)).
        { intros x Hx NE. rewrite EMf in NE.
          destruct (decide (Mpre (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite <- E4 in NE. right; right; right. unfold errno12, A_ERRNO, TPV in *. wdiff NE Mpre x.
          - destruct (MpreW x Hx NE4) as [W|[W|W]]; [left; exact W | right; left; exact W | right; right; left; exact W]. }
        assert (AGf : forall a1 k v, cell M a1 k v -> IMG_LO <= a1 -> a1 + Z.of_nat k <= IMG_HI ->
                       (forall y, a1 <= y < a1 + Z.of_nat k -> ~ (((ctx_brk <= y < ctx_brk + 8) \/ (ctx_avail_meta_area_count <= y < ctx_avail_meta_area_count + 16) \/
                                                               (ctx_avail_meta_areas <= y < ctx_avail_meta_areas + 8)) \/ (A_ERRNO <= y < A_ERRNO + 4))) -> cell Mf a1 k v).
        { intros a1 k v C Ha Hk OUT. eapply (cell_keep Mf _ a1 k v); [| exact C | exact Ha | exact Hk | exact OUT].
          intros y Hy NE. destruct (MfW y Hy NE) as [A|[A|[A|A]]]; [left; right; ceil; lia | right; left; exact A | left; clear -A HI; lia | right; right; exact A]. }
        assert (STKf : forall d v, 8 <= d <= 56 -> rdn RSEGS M1 (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v) ->
                       rdn RSEGS Mf (Z_to_bv 64 (sp - d)) 8%nat = Some (word_to_le_bytes 8 v)).
        { intros d v Hd R. rewrite <- (MmS (sp - d) 8%nat _ ltac:(lia) ltac:(cbn; lia) R). symmetry. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
          intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
          rewrite EMf. unfold Mpre, Mm5, mp_frame, Mm4, errno12, A_ERRNO, TPV, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX.
          rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). rewrite (Mm3out (bv_unsigned x)) by lia.
          unfold Mm2, mm_frame. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity. }
        destruct (amPf Mf sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) Hsp64 Hra
                    ltac:(pose proof (rc_canary st M (rp_statics st M HREP)) as C; unfold cell in C; apply (AGf _ _ _ C); unfold A_CANARY, ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX, A_ERRNO, TPV; cbn; intros; lia)
                    (STKf 56 _ ltac:(lia) (UbMhAMetaS.M1_can st X M regs sp Hsp)) (STKf 8 _ ltac:(lia) (UbMhAMetaS.M1_ra st X M regs sp Hsp))
                    (STKf 16 _ ltac:(lia) (UbMhAMetaS.M1_s0 st X M regs sp Hsp)) (STKf 24 _ ltac:(lia) (UbMhAMetaS.M1_s1 st X M regs sp Hsp))
                    (STKf 32 _ ltac:(lia) (UbMhAMetaS.M1_s2 st X M regs sp Hsp)) (STKf 40 _ ltac:(lia) (UbMhAMetaS.M1_s3 st X M regs sp Hsp))
                    (STKf 48 _ ltac:(lia) (UbMhAMetaS.M1_s4 st X M regs sp Hsp))
                    ltac:(rewrite EMf; unfold errno12; pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 12)) Mpre (Z_to_bv 64 A_ERRNO)) as RH;
                          rewrite length_N_to_le_bytes in RH; apply RH; unfold A_ERRNO, TPV; zsimp; lia)
                    rF rom F2 ltac:(kept_rw KF; gres; kept_rw KS; kept_rw KQ; rewrite P18; exact R18) F10
                    ltac:(kept_rw KF; gres; kept_rw KS; kept_rw KQ; kept_rw KP; gres; kept_rw KN; exact R4))
          as (rZ & RUNZ & Z2 & Z10 & Z1 & Z8 & Z9 & Z18 & Z19 & Z20 & KZ).
        replace (Z_to_bv 64 421664) with (421664%bv : word) by (apply bv_eq; reflexivity).
        eapply (kf_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUNZ |].
        apply Hfail. rewrite EMf.
        assert (MpreG : forall y, 0 <= y < 2 ^ 64 -> ~ (p0 <= y < p0 + N) -> M (Z_to_bv 64 y) <> None -> Mpre (Z_to_bv 64 y) <> None).
        { intros y Hy OUT D. unfold Mpre, Mm5, mp_frame, Mm4. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). rewrite (Mm3out y Hy OUT).
          apply Mm2G. exact D. }
        apply (am_fail_fst (v_regions st p0) (d_brk st true) (p0 + 4096) (v_ac st) (sh + 1) (d_cb st true) Mpre _ mdl1 rZ).
        - exact (v_WF st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF HI true).
        - apply (f_REP st L M Mpre HWF HREP (v_regions st p0) (d_brk st true) (p0 + 4096) (v_ac st) (sh + 1) (d_cb st true));
            [exact (v_Hac' st L HWF Hcnt Hac p0) | exact (v_Hsh' st L HWF Hcnt Hac p0) | ..].
          + intros a1 Hr Ha. destruct (decide (Mpre (Z_to_bv 64 a1) = M (Z_to_bv 64 a1))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a1 Hr NE) as [W|[W|W]]; [ceil; unfold CTX in *; lia | unfold ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX in *; lia | unfold CTX in *; lia].
          + intros a1 Hr [Ha NW]. destruct (decide (Mpre (Z_to_bv 64 a1) = M (Z_to_bv 64 a1))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a1 Hr NE) as [W|[W|W]]; [ceil; unfold CTX_END, CTX in *; lia | | unfold CTX_END, CTX in *; lia].
            apply NW. unfold fctxW. unfold ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX in *. lia.
          + unfold v_ac, cell, Mpre, Mm5, mp_frame, Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *. do 5 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
          + unfold cell, Mpre, Mm5, mp_frame, Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *. do 4 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
          + unfold cell, Mpre, Mm5, mp_frame, Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
          + unfold d_cb. unfold cell, Mpre, Mm5, mp_frame, Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, ctx_brk, CTX in *. do 6 rdn_peel1.
            unfold Mm3. rewrite rdn_unfill_outZ by (unfold HEAPLO in *; cbn; lia). unfold Mm2, mm_frame. do 7 rdn_peel1. exact MmB.
          + intros a1 Hd D. apply MpreG; [exact (UbMhAMetaT.dfoot_rng st L X HWF a1 Hd) | | exact D].
            intros IN. destruct Hd as [Hd|[Hd|[Hd|(t & Ht & Kt & Rt)]]].
            * unfold A_ERRNO, TPV in *. lia.
            * unfold CTX_END, CTX in *. lia.
            * destruct Hd as (ar & Har & Ra). destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Y1 & Y2). destruct (AP rr Hrr); lia.
            * pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
              destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; lia.
          + intros ar a1 Har Ha. destruct (wa_rng st (WF_areas st L HWF) ar Har) as (Aal & Alo & Ahi).
            destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Y1 & Y2). pose proof (AP rr Hrr) as D.
            destruct (decide (Mpre (Z_to_bv 64 a1) = M (Z_to_bv 64 a1))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a1 ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[W|W]]; [ceil; lia | unfold ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX in *; lia | lia].
          + intros t a1 Ht Kt Ha. destruct (group_range st L HWF t Ht) as [G1 G2].
            pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD. rewrite Kt in KD. destruct KD as (K1 & K2 & _).
            destruct (wr_rng st (WF_regions st L HWF) _ K2) as (W1 & W2 & _). cbn in W1, W2. pose proof (region_img st L HWF _ K2) as RI. cbn [rg_base rg_len] in RI.
            pose proof (AP _ K2) as D. cbn in D. unfold g_map_end in Ha.
            destruct (decide (Mpre (Z_to_bv 64 a1) = M (Z_to_bv 64 a1))) as [E|NE]; [exact E|]. exfalso.
            destruct (MpreW a1 ltac:(ceil; unfold HEAPLO in *; lia) NE) as [W|[W|W]]; [ceil; lia | unfold ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX in *; lia | lia].
        - apply (v_ledger st L X (m_vmmaps mdl) HWF HLG Hcnt Hac p0 HP0 true); rewrite ?MF1; try reflexivity. intros E; discriminate E.
        - apply errno_write_intro.
        - rewrite MF2; exact Hh. - rewrite MF3; exact Hlz. - rewrite MF4; exact Hmat. - exact MF5. - exact MF6. - rewrite MF1; reflexivity.
        - split; [cbn [s_regions fst]; rewrite (v_RSUM st p0); lia|]. split; [cbn [s_regions fst]; rewrite (v_len st p0); lia|].
          cbn [s_regions fst]. exact (v_new_apart_X st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF).
        - exact Z10.
        - rewrite Z2, H2. reflexivity.
        - apply (UbMhAMetaS.keeps_final_am regs rZ (bigM ++ (clobMM1 ++ ([10]%bv ++ ([1; 2; 8; 9; 11; 18; 19; 20; 21]%bv ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ ([1; 2; 8; 10; 11]%bv ++ clobZ))))))))).
          + eapply UbMhAMetaS.keeps_join; [exact KM|]. eapply UbMhAMetaS.keeps_join; [exact KN|].
            eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
            eapply UbMhAMetaS.keeps_join; [exact KP|]. eapply UbMhAMetaS.keeps_join; [exact KQ|]. eapply UbMhAMetaS.keeps_join; [exact KS|].
            eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
            eapply UbMhAMetaS.keeps_join; [exact KF | exact KZ].
          + rewrite forallb_app, COVM. reflexivity.
          + exact Z1. + rewrite Z2, H2; reflexivity. + exact Z8. + exact Z9. + exact Z18. + exact Z19. + exact Z20.
          + kept_rw KZ. kept_rw KF. gres. kept_rw KS. kept_rw KQ. rewrite P21. exact R21.
        - intros a1 Ha NE. rewrite <- EMf in NE. destruct (MfW a1 Ha NE) as [W|[W|[W|W]]].
          + left. unfold AMSTK. exact W.
          + right; left. unfold ctx_brk, ctx_avail_meta_area_count, ctx_avail_meta_areas, CTX_END, CTX in *. lia.
          + right; right; right. exists (v_Rn st p0). split; [left; reflexivity|]. unfold v_Rn. cbn. split; [intros y E; discriminate E | lia].
          + right; right; left. exact W.
        - rewrite <- EMf. intros y Hy. unfold Mf, mp_ffail, Mm5, mp_frame. do 4 apply (wbytes_grows _ _ _ (Z_to_bv 64 y)). apply D4. exact Hy. }
      (* [comment removed for export] *)
      unfold mpr_ok. rewrite pru_4096. replace (v_addi (0x68404%bv : word) 4) with (0x68408%bv : word) by (apply bv_eq; reflexivity).
      set (Mm6 := zfill (Z_to_bv 64 (p0 + 4096)) (Z_to_bv 64 4096) Mm5).
      set (mdl2 := mprotect_model (Z_to_bv 64 (p0 + 4096)) (Z_to_bv 64 4096) mdl1).
      pose (h2 := mkVmMapsFull (vm_reserved (m_vmmaps mdl1)) (vm_maps (m_vmmaps mdl1))
                 (maps_subtract (vm_noaccess (m_vmmaps mdl1)) (bv_unsigned (Z_to_bv 64 (p0 + 4096))) (bv_unsigned (Z_to_bv 64 (p0 + 4096)) + bv_unsigned (Z_to_bv 64 4096)))
                 (vm_start_brk (m_vmmaps mdl1)) (vm_brk (m_vmmaps mdl1)) (vm_limit (m_vmmaps mdl1)) (vm_mmap_base (m_vmmaps mdl1)) (vm_init_sp (m_vmmaps mdl1))).
      pose proof (with_vmmaps_facts h2 mdl1) as MG. change (with_vmmaps h2 mdl1) with mdl2 in MG. destruct MG as (MG1 & MG2 & MG3 & MG4 & MG5 & MG6).
      (* [comment removed for export] *)
      assert (RA6 : rdn RSEGS Mm6 (Z_to_bv 64 (sp - 64 - 8)) 8%nat = Some (word_to_le_bytes 8 (getr rQ 1))).
      { unfold Mm6, Mm5, mp_frame. rewrite rdn_zfill_outZ by (cbn; lia). apply rdn_wbytes_hit8. zsimp; lia. }
      destruct (mpW2 (sp - 64) (p0 + 4096) ltac:(lia) (regupd rS 10 (Z_to_bv 64 0)) rom Mm6 (getr rQ 1) ltac:(rewrite U1; apply ret_ok_even; reflexivity)
                  ltac:(gres; exact V2) ltac:(gres; reflexivity) RA6) as (rF & RUN6 & F2 & F10 & F1 & KF).
      eapply (kfx_msteps RSEGS F HL); [rewrite MG2, MF2; exact Hh | rewrite MG3, MF3; exact Hlz | exact RUN6 |].
      rewrite U1. replace (Z_to_bv 64 421664) with (421664%bv : word) by (apply bv_eq; reflexivity).
      eapply (kfx_msteps RSEGS F HL); [rewrite MG2, MF2; exact Hh | rewrite MG3, MF3; exact Hlz | exact (amC1b rF rom Mm6 F10) |].
      (* [comment removed for export] *)
      assert (KT : keeps_but (bigM ++ (clobMM1 ++ ([10]%bv ++ ([1; 2; 8; 9; 11; 18; 19; 20; 21]%bv ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ [1; 2; 10; 11]%bv))))))) regs rF).
      { eapply UbMhAMetaS.keeps_join; [exact KM|]. eapply UbMhAMetaS.keeps_join; [exact KN|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity]|].
        eapply UbMhAMetaS.keeps_join; [exact KP|]. eapply UbMhAMetaS.keeps_join; [exact KQ|]. eapply UbMhAMetaS.keeps_join; [exact KS|].
        eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KF]. }
      assert (M6W : forall x, 0 <= x < 2 ^ 64 -> Mm6 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - AMSTK <= x < sp) \/ ctxV x \/ (p0 <= x < p0 + N)).
      { intros x Hx NE. unfold Mm6 in NE.
        destruct (decide (zfill (Z_to_bv 64 (p0 + 4096)) (Z_to_bv 64 4096) Mm5 (Z_to_bv 64 x) = Mm5 (Z_to_bv 64 x))) as [E0|NE0].
        - rewrite E0 in NE. destruct (Mm5W x Hx NE) as [W|[W|W]]; [left; unfold AMSTK; lia | right; left; unfold UbMhAMetaT.ctxV; clear -W; tauto | right; right; exact W].
        - right; right. pose proof (zfill_diffZ _ (p0 + 4096) 4096 x ltac:(lia) ltac:(lia) ltac:(lia) Hx NE0). lia. }
      apply (kfx_kat RSEGS F HL bi _ (kfx bi)); [|intros c' Hc'; exact Hc'].
      apply (UbMhAMetaT.am_tail st L X M mdl regs rom sp (kfx bi) HWF HREP HCNT H2 Hra Hsp Hok
               rF Mm6 mdl2 (p0 + 4096) (UbMhAMetaR.c4_regions st p0) (UbMhAMetaR.c4_brk st) (2 * 2 ^ sh - 1) (sh + 1) (2 ^ 64 - 1) (s_errno st) (fun x => p0 <= x < p0 + N)
               (bigM ++ (clobMM1 ++ ([10]%bv ++ ([1; 2; 8; 9; 11; 18; 19; 20; 21]%bv ++ ([1; 9; 10; 11; 12]%bv ++ ([2; 11; 13; 14; 17]%bv ++ ([10]%bv ++ [1; 2; 10; 11]%bv))))))) Hfl Hac0).
      - exact F2.
      - kept_rw KF. gres. kept_rw KS. exact U9.
      - kept_rw KF. gres. kept_rw KS. kept_rw KQ. rewrite P19. exact R19.
      - kept_rw KF. gres. kept_rw KS. kept_rw KQ. rewrite P18. exact R18.
      - kept_rw KF. gres. kept_rw KS. kept_rw KQ. rewrite P21. exact R21.
      - exact KT.
      - rewrite forallb_app, COVM. reflexivity.
      - rewrite MG2, MF2; exact Hh. - rewrite MG3, MF3; exact Hlz. - rewrite MG4, MF4; exact Hmat. - rewrite MG5, MF5; reflexivity. - rewrite MG6, MF6; reflexivity.
      - rewrite MG1. unfold h2. cbn [vm_limit]. rewrite MF1. reflexivity.
      - intros x Hx NE. destruct (M6W x Hx NE) as [W|[W|W]]; [left; exact W | right; left; exact W | right; right; left; exact W].
      - (* [comment removed for export] *) pose proof (rc_errno st M (rp_statics st M HREP)) as C.
        eapply cell_agree; [unfold A_ERRNO, TPV; lia | unfold A_ERRNO, TPV; cbn; lia | | exact C]. intros y Hr Hy. cbn in Hy.
        destruct (decide (Mm6 (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
        destruct (M6W y Hr NE) as [W|[W|W]]; unfold UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W HI Hy; lia].
      - intros y Hy NE. exfalso. destruct (M6W y ltac:(unfold A_ERRNO, TPV in Hy; lia) NE) as [W|[W|W]];
          unfold UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W HI Hy; lia].
      - left; reflexivity.
      - (* [comment removed for export] *) intros x Hx. split; [unfold HEAPLO; lia|]. split; [lia|]. split.
        + intros ar Har IN. destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Z1 & Z2). destruct (AP rr Hrr); lia.
        + intros t Ht Kt IN. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
          destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end in IN; lia.
      - intros x Hx. left. exists (UbMhAMetaR.c4_Rn st p0). split; [left; reflexivity|]. unfold UbMhAMetaR.c4_Rn. cbn. split; [intros y E; discriminate E | lia].
      - (* [comment removed for export] *)
        intros x Hd D. unfold Mm6. apply zfill_grows. unfold Mm5, mp_frame. apply wbytes_grows. unfold Mm4. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 x)).
        pose proof (UbMhAMetaT.dfoot_rng st L X HWF x Hd) as XR. rewrite (Mm3out x XR).
        + apply Mm2G. exact D.
        + intros IN. destruct Hd as [Hd|[Hd|[Hd|(t & Ht & Kt & Rt)]]].
          * unfold A_ERRNO, TPV in *. lia.
          * unfold CTX_END, CTX in *. lia.
          * destruct Hd as (ar & Har & Ra). destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Z1 & Z2). destruct (AP rr Hrr); lia.
          * pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
            destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; lia.
      - (* [comment removed for export] *) intros x Hx. unfold Mm6. apply zfill_inZ; lia.
      - (* [comment removed for export] *) unfold Mm6. eapply defined_grows; [apply zfill_grows|]. unfold Mm5, mp_frame. apply defined_wbytes. exact D4.
      - (* [comment removed for export] *) unfold cell, Mm6, Mm5, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_avail_meta_area_count, CTX; cbn; lia).
        unfold Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *. do 3 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
      - unfold cell, Mm6, Mm5, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_meta_alloc_shift, CTX; cbn; lia).
        unfold Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX in *. do 2 rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
      - unfold cell, Mm6, Mm5, mp_frame. rewrite rdn_zfill_outZ by (unfold ctx_brk, CTX; cbn; lia).
        unfold Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, ctx_brk, CTX in *. do 4 rdn_peel1.
        unfold Mm3. rewrite rdn_unfill_outZ by (unfold HEAPLO in *; cbn; lia). unfold Mm2, mm_frame. do 7 rdn_peel1. unfold cell, ctx_brk, CTX in MmB. exact MmB.
      - assert (1 <= 2 ^ sh) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia). assert (P11 : 2 ^ sh <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). cbn in P11. lia.
      - exact (UbMhAMetaR.c4_Hp st L HWF Hcnt Hac p0 HP0).
      - exact (UbMhAMetaR.c4_Hp_img st L HWF Hcnt Hac p0 HI).
      - exact (UbMhAMetaR.c4_Hp_areas st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF).
      - exact (UbMhAMetaR.c4_Hp_groups st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF).
      - exact Hcnt.
      - exact (UbMhAMetaR.c4_HRgrp st p0).
      - exact (UbMhAMetaR.c4_HRsub st p0).
      - exact (UbMhAMetaR.c4_HRold st L HWF p0).
      - exact (UbMhAMetaR.c4_HRnew st L HWF Hcnt Hac p0).
      - pose proof (UbMhAMetaR.c4_Hcur' st L HWF Hcnt Hac p0) as HC. unfold UbMhAMetaR.c4_ac, UbMhAMetaR.c4_p in HC. unfold UbMhAMetaR.c4_p.
        replace (2 * 2 ^ sh - 1 - 1) with (2 * 2 ^ sh - 2) by lia. exact HC.
      - pose proof (UbMhAMetaR.c4_Hsh' st L HWF Hcnt Hac p0) as HS. unfold UbMhAMetaR.c4_ac in HS. replace (2 * 2 ^ sh - 1 - 1) with (2 * 2 ^ sh - 2) by lia. exact HS.
      - pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. pose proof (wc_shift st (WF_ctx st L HWF)) as SR.
        rewrite Hac in SA. replace (sh + 1 + 1) with (sh + 2) by lia.
        rewrite (Z.pow_add_r 2 sh 2), (Z.pow_add_r 2 sh 1) in * by lia. change (2 ^ 2) with 4 in *. change (2 ^ 1) with 2 in *. clear -SA SR. lia.
      - exact (UbMhAMetaR.c4_Hbrk' st).
      - pose proof (UbMhAMetaR.c4_t_wf_regions st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF) as WR. unfold UbMhAMetaR.c4_st, UbMhAMetaR.c4_ac, UbMhAMetaR.c4_p in WR.
        replace (2 * 2 ^ sh - 1 - 1) with (2 * 2 ^ sh - 2) by lia. exact WR.
      - pose proof (UbMhAMetaR.c4_t_wf_img st L HWF Hcnt Hac p0 HI) as WI. unfold UbMhAMetaR.c4_st, UbMhAMetaR.c4_ac, UbMhAMetaR.c4_p in WI.
        replace (2 * 2 ^ sh - 1 - 1) with (2 * 2 ^ sh - 2) by lia. exact WI.
      - rewrite MG1. unfold h2. rewrite MF1. unfold h1. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp].
        pose proof (UbMhAMetaR.c4_t_ledger st L X (m_vmmaps mdl) HWF HLG XOK Hcnt Hac p0 HP0 HRF) as LG.
        unfold UbMhAMetaR.c4_st, UbMhAMetaR.c4_vm, UbMhAMetaR.c4_ac, UbMhAMetaR.c4_p in LG. rewrite !u_Z2bv by lia.
        replace (2 * 2 ^ sh - 1 - 1) with (2 * 2 ^ sh - 2) by lia. replace (p0 + 4096 + 4096) with (p0 + 8192) by lia. exact LG.
      - unfold UbMhAMetaR.c4_regions. rewrite RSUM_cons. cbn [rg_len UbMhAMetaR.c4_Rn]. lia.
      - unfold UbMhAMetaR.c4_regions. cbn [length]. lia.
      - exact (UbMhAMetaR.c4_new_apart_X st L X _ HWF HLG XOK Hcnt Hac p0 HP0 HRF).
      - (* [comment removed for export] *)
        intros t Ht Kt. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
        destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end; lia.
      - (* [comment removed for export] *)
        intros x n bs Hx Hn R. unfold Mm6, Mm5, mp_frame. rewrite rdn_zfill_outZ by lia. rdn_peel1.
        unfold Mm4, ctx_avail_meta_area_count, ctx_meta_alloc_shift, ctx_avail_meta_areas, CTX. do 3 rdn_peel1.
        unfold Mm3. rewrite rdn_unfill_outZ by lia. unfold Mm2, mm_frame. do 7 rdn_peel1. exact (MmS x n bs Hx Hn R).
    Qed.
  End ArmMM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma x4_clobI : forall r1, keeps_but clobI regs r1 -> getr r1 4 = Z_to_bv 64 TPV.
  Proof using H4. intros r1 K1. kept_rw K1. exact H4. Qed.

  Section ArmC4d.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    Hypothesis Hac : c_area_cnt cx = 0.
    Variable gd : option (Z * gkd).
    Hypothesis HBD : s_brk st = BrkDead gd.

    Lemma arm_C4d : forall b r1, getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kfx b (mkCfg (mkst r1 (0x66d1c%bv : word) M1 rom) mdl).
    Proof using HBD gd Hac Hac0 Hfl Hfail Hok DEF H4 Hsp Hra H2 HBUD HLEN HCNT Hmat Hlz Hh XOK HLG HREP HWF HL bi X L RN.
      intros b r1 G2 G19 G8 G18 K1. pose proof Hsp' as [S1 S2]. ceil.
      pose proof (HCNT Hfl Hac0) as Hcnt. pose proof (UbMhAMetaR.c4_sh_rng st L HWF Hcnt Hac 0) as [SH1 SH2].
      pose proof (UbMhAMetaS.M1_REP st L X M regs sp HWF HREP Hsp) as REP1. pose proof (rp_ctx st M1 REP1) as RC1.
      pose proof (rc_fmh st M1 RC1) as Cfh. rewrite (wc_fhead st (WF_ctx st L HWF)), Hfl in Cfh. cbn [head_of] in Cfh.
      pose proof (rc_amc st M1 RC1) as Ccnt. rewrite Hac0 in Ccnt.
      pose proof (rc_amac st M1 RC1) as Cac. rewrite Hac in Cac.
      pose proof (rc_brk st M1 RC1) as Cbrk. pose proof (wc_brk st (WF_ctx st L HWF)) as WB. rewrite HBD in WB. rewrite WB in Cbrk.
      destruct (amD M1 Cfh Ccnt 0 (2 ^ 64 - 1) Cac Cbrk r1 rom G19 G8 eq_refl eq_refl) as (rD & RUN1 & KD).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
      destruct (amMM rD rom M1 (c_shift cx) ltac:(lia) ltac:(kept_rw KD; exact G19) ltac:(kept_rw KD; exact G8) (rc_mas st M1 RC1))
        as (rM & RUN2 & R10 & R11 & R12 & R13 & R14 & R15 & R9 & R20 & R1 & KM).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN2 |].
      apply (arm_MM Hfl Hac0 Hac rM M1 (clobI ++ ([9; 10; 11]%bv ++ [1; 9; 10; 11; 12; 13; 14; 15; 20]%bv))).
      - kept_rw KM. kept_rw KD. exact G2.
      - exact R10. - unfold UbMhAMetaR.c4_N. exact R11. - exact R12. - exact R13. - exact R14. - exact R15. - exact R9. - exact R20. - exact R1.
      - kept_rw KM. kept_rw KD. exact G19.
      - kept_rw KM. kept_rw KD. exact G8.
      - kept_rw KM. kept_rw KD. exact G18.
      - kept_rw KM. kept_rw KD. kept_rw K1. reflexivity.
      - kept_rw KM. kept_rw KD. exact (x4_clobI r1 K1).
      - eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KD | exact KM].
      - reflexivity.
      - intros a Ha NE. left. exact (UbMhAMetaS.M1_writes st X M regs sp Hsp a Ha NE).
      - exact Cbrk.
      - exact (UbMhAMetaS.M1_grows st M regs sp).
      - intros a n bs _ _ R. exact R.
      - exact (UbMhAMetaS.M1_def st M regs sp DEF).
    Qed.
  End ArmC4d.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ArmC3.
    Hypothesis Hfl : s_flist st = [].
    Hypothesis Hac0 : c_avail_cnt cx = 0.
    Hypothesis Hac : c_area_cnt cx = 0.
    Variables (b0 bk : Z) (gk : gkd).
    Hypothesis HBL : s_brk st = BrkLive b0 bk gk.

    Lemma arm_C3 : forall bo r1, (bo = true -> bi = true) ->
      getr r1 2 = Z_to_bv 64 (sp - 64) -> getr r1 19 = Z_to_bv 64 MLOCK -> getr r1 8 = Z_to_bv 64 4096 ->
      getr r1 18 = Z_to_bv 64 A_CANARY -> keeps_but clobI regs r1 ->
      kfx bo (mkCfg (mkst r1 (0x66d1c%bv : word) M1 rom) mdl).
    Proof using HBL gk bk b0 Hac Hac0 Hfl Hfail Hok DEF H4 Hsp Hra H2 HBUD HLEN HCNT Hmat Hlz Hh XOK HLG HREP HWF HL X L RN.
      intros bo r1 Hside G2 G19 G8 G18 K1. pose proof Hsp' as [S1 S2]. ceil.
      pose proof (HCNT Hfl Hac0) as Hcnt. pose proof (UbMhAMetaR.c4_sh_rng st L HWF Hcnt Hac 0) as [SH1 SH2].
      pose proof (UbMhAMetaS.M1_REP st L X M regs sp HWF HREP Hsp) as REP1. pose proof (rp_ctx st M1 REP1) as RC1.
      pose proof (rc_fmh st M1 RC1) as Cfh. rewrite (wc_fhead st (WF_ctx st L HWF)), Hfl in Cfh. cbn [head_of] in Cfh.
      pose proof (rc_amc st M1 RC1) as Ccnt. rewrite Hac0 in Ccnt.
      pose proof (rc_amac st M1 RC1) as Cac. rewrite Hac in Cac.
      pose proof (rc_brk st M1 RC1) as Cbrk. pose proof (wc_brk st (WF_ctx st L HWF)) as WB. rewrite HBL in WB.
      destruct WB as (Ecb & B0al & Bal & B0lo & B0b & Bce). rewrite Ecb in Cbrk.
      pose proof (lx_brk st X _ HLG) as LB. rewrite HBL in LB. destruct LB as [LB1 LB2].
      destruct (amB4 M1 Cfh Ccnt 0 bk ltac:(lia) Cac Cbrk r1 rom G19 G8 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as (rB & RUN1 & B10 & B9 & B17 & KB).
      eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
      (* [comment removed for export] *)
      assert (EB : vm_brk (m_vmmaps mdl) = Z_to_bv 64 bk) by (symmetry; apply Z_to_bv_u_eq'; symmetry; exact LB1).
      apply (kfx_brk_grow RSEGS F HL bo rB (0x66d94%bv : word) M1 rom mdl W_66d40 4096 Hh Hlz F_66d40 E_66d40 B17);
        rewrite ?LB1, ?LB2; [unfold page_size; exact Bal | reflexivity | lia | lia | lia | lia | exact B10 | |].
      - (* [comment removed for export] *)
        replace (v_addi (0x66d94%bv : word) 4) with (0x66d98%bv : word) by (apply bv_eq; reflexivity).
        rewrite EB.
        eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact (amB5r (regupd rB 10 (Z_to_bv 64 bk)) rom M1 (bk + 4096) bk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact B9)) |].
        destruct (amRef (regupd rB 10 (Z_to_bv 64 bk)) rom M1 (c_shift cx) ltac:(lia) ltac:(gres; kept_rw KB; exact G19) ltac:(gres; kept_rw KB; exact G8) Cac (rc_mas st M1 RC1) (ctx_sok M1))
          as (rM & RUN2 & R10 & R11 & R12 & R13 & R14 & R15 & R9 & R20 & R1 & KM).
        eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN2 |].
        set (Mm := wbytes M1 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 64 - 1)))).
        apply (arm_MM Hfl Hac0 Hac rM Mm (clobI ++ ([9; 10; 11; 17]%bv ++ ([10]%bv ++ [1; 9; 10; 11; 12; 13; 14; 15; 20]%bv)))).
        + kept_rw KM. gres. kept_rw KB. exact G2.
        + exact R10. + unfold UbMhAMetaR.c4_N. exact R11. + exact R12. + exact R13. + exact R14. + exact R15. + exact R9. + exact R20. + exact R1.
        + kept_rw KM. gres. kept_rw KB. exact G19.
        + kept_rw KM. gres. kept_rw KB. exact G8.
        + kept_rw KM. gres. kept_rw KB. exact G18.
        + kept_rw KM. gres. kept_rw KB. kept_rw K1. reflexivity.
        + kept_rw KM. gres. kept_rw KB. exact (x4_clobI r1 K1).
        + eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KB|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KM].
        + reflexivity.
        + intros a Ha NE. unfold Mm in NE.
          destruct (decide (wbytes M1 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 64 - 1))) (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E0|NE0].
          * rewrite E0 in NE. left. exact (UbMhAMetaS.M1_writes st X M regs sp Hsp a Ha NE).
          * right. unfold ctx_brk, CTX in *. apply wbytes_diff_g in NE0; [| lia | zsimp; lia | exact Ha]. rewrite length_N_to_le_bytes in NE0. cbn in NE0. lia.
        + unfold cell, Mm, ctx_brk, CTX. apply rdn_wbytes_hit8. zsimp; lia.
        + unfold Mm. eapply mem_grows_trans; [exact (UbMhAMetaS.M1_grows st M regs sp) | apply wbytes_grows].
        + intros a n bs Ha Hn R. unfold Mm, ctx_brk, CTX. rdn_peel1. exact R.
        + unfold Mm. apply defined_wbytes. exact (UbMhAMetaS.M1_def st M regs sp DEF).
      - (* [comment removed for export] *)
        intros GOK. replace (v_addi (0x66d94%bv : word) 4) with (0x66d98%bv : word) by (apply bv_eq; reflexivity). rewrite <- LB1 in GOK.
        pose proof (brk_grow_ok_facts mdl 4096 ltac:(lia) ltac:(rewrite LB1; lia) ltac:(rewrite LB1; lia) ltac:(rewrite LB1; unfold page_size; exact Bal) ltac:(reflexivity) GOK) as (GF1 & GF2 & GF3).
        rewrite LB1 in GF1.
        assert (EB' : vm_brk (m_vmmaps mdl) = Z_to_bv 64 bk) by exact EB.
        rewrite EB in GF2 |- *.
        (* [comment removed for export] *)
        assert (Hce : bk + 4096 <= CEIL).
        { apply (grant_end_le_CEIL (m_vmmaps mdl) bk 4096 (lx_top st X _ HLG)); try lia. rewrite Z.add_mod, Bal by lia. reflexivity. }
        set (M2 := zfill (Z_to_bv 64 bk) (Z_to_bv 64 4096) M1).
        eapply (kfx_msteps RSEGS F HL); [| | exact (amB5g (regupd rB 10 (Z_to_bv 64 (bk + 4096))) rom M2 (bk + 4096) ltac:(lia) ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity) ltac:(gres; exact B9)) |].
        { pose proof (with_vmmaps_facts (brk_grow_vm (m_vmmaps mdl) 4096) mdl) as (_ & X2 & _). rewrite X2. exact Hh. }
        { pose proof (with_vmmaps_facts (brk_grow_vm (m_vmmaps mdl) 4096) mdl) as (_ & _ & X3 & _). rewrite X3. exact Hlz. }
        destruct (amB3 (regupd rB 10 (Z_to_bv 64 (bk + 4096))) rom M2 (bk + 4096) ltac:(lia) ltac:(gres; exact B9) ltac:(gres; kept_rw KB; exact G19) ltac:(gres; kept_rw KB; exact G8) (ctx_sok M2))
          as (rT & RUN3 & T9 & T8 & KT0).
        set (mdl1 := with_vmmaps (brk_grow_vm (m_vmmaps mdl) 4096) mdl).
        pose proof (with_vmmaps_facts (brk_grow_vm (m_vmmaps mdl) 4096) mdl) as MF. change (with_vmmaps (brk_grow_vm (m_vmmaps mdl) 4096) mdl) with mdl1 in MF.
        destruct MF as (MF1 & MF2 & MF3 & MF4 & MF5 & MF6).
        eapply (kfx_msteps RSEGS F HL); [rewrite MF2; exact Hh | rewrite MF3; exact Hlz | exact RUN3 |].
        set (M3 := wbytes (wbytes M2 (Z_to_bv 64 ctx_brk) (word_to_le_bytes 8 (Z_to_bv 64 (bk + 4096)))) (Z_to_bv 64 ctx_avail_meta_area_count) (word_to_le_bytes 8 (Z_to_bv 64 1))).
        assert (HRF : region_free (vm_reserved (m_vmmaps mdl) ++ vm_maps (m_vmmaps mdl)) (Z_to_bv 64 bk) (Z_to_bv 64 4096) = true).
        { pose proof GF2 as RF8. unfold page_size in RF8. replace (4096 + 4096) with 8192 in RF8 by reflexivity.
          apply (UbMhAMetaT.region_free_shrink st X _ bk 8192 bk 4096); try lia. exact RF8. }
        pose proof (UbMhAMetaR.c3_apart st L X _ HWF HLG XOK b0 bk gk HBL Hce HRF) as [AP APX].
        assert (M3W : forall x, 0 <= x < 2 ^ 64 -> M3 (Z_to_bv 64 x) <> M (Z_to_bv 64 x) -> (sp - AMSTK <= x < sp) \/ ctxV x \/ (bk <= x < bk + 4096)).
        { intros x Hx NE. unfold M3 in NE.
          destruct (decide (M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x))) as [E4|NE4].
          - rewrite <- E4 in NE. right; left. unfold UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX in NE |- *. wdiff NE M2 x.
          - unfold M2 in NE4. destruct (decide (zfill (Z_to_bv 64 bk) (Z_to_bv 64 4096) M1 (Z_to_bv 64 x) = M1 (Z_to_bv 64 x))) as [E5|NE5].
            + rewrite E5 in NE4. left. pose proof (UbMhAMetaS.M1_writes st X M regs sp Hsp x Hx NE4). unfold AMSTK. lia.
            + right; right. exact (zfill_diffZ _ bk 4096 x ltac:(lia) ltac:(lia) ltac:(lia) Hx NE5). }
        apply (kfx_kat RSEGS F HL bo _ (kfx bo)); [|intros c' Hc'; exact Hc'].
        apply (UbMhAMetaT.am_tail st L X M mdl regs rom sp (kfx bo) HWF HREP HCNT H2 Hra Hsp (fun c' Hc' => kfx_mono RSEGS F HL bi bo c' Hside (Hok c' Hc'))
                 rT M3 mdl1 bk (UbMhAMetaR.c3_regions st bk) (UbMhAMetaR.c3_brk b0 bk gk) 1 (c_shift cx) (bk + 4096) (s_errno st) (fun x => bk <= x < bk + 4096)
                 (clobI ++ ([9; 10; 11; 17]%bv ++ ([10]%bv ++ [8; 9]%bv))) Hfl Hac0).
        + kept_rw KT0. gres. kept_rw KB. exact G2.
        + rewrite T9. f_equal. lia.
        + kept_rw KT0. gres. kept_rw KB. exact G19.
        + kept_rw KT0. gres. kept_rw KB. exact G18.
        + kept_rw KT0. gres. kept_rw KB. kept_rw K1. reflexivity.
        + eapply UbMhAMetaS.keeps_join; [exact K1|]. eapply UbMhAMetaS.keeps_join; [exact KB|]. eapply UbMhAMetaS.keeps_join; [apply keeps_but_upd; [apply keeps_but_refl | left; reflexivity] | exact KT0].
        + reflexivity.
        + rewrite MF2; exact Hh. + rewrite MF3; exact Hlz. + rewrite MF4; exact Hmat. + exact MF5. + exact MF6. + rewrite MF1; reflexivity.
        + intros x Hx NE. destruct (M3W x Hx NE) as [W|[W|W]]; [left; exact W | right; left; exact W | right; right; left; exact W].
        + (* [comment removed for export] *) pose proof (rc_errno st M (rp_statics st M HREP)) as C. pose proof (UbMhAMetaR.c3_b_facts st L X _ HWF HLG b0 bk gk HBL) as BF.
          eapply cell_agree; [unfold A_ERRNO, TPV; lia | unfold A_ERRNO, TPV; cbn; lia | | exact C]. intros y Hr Hy. cbn in Hy.
          destruct (decide (M3 (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
          destruct (M3W y Hr NE) as [W|[W|W]]; unfold UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W BF Hy; lia].
        + intros y Hy NE. exfalso. pose proof (UbMhAMetaR.c3_b_facts st L X _ HWF HLG b0 bk gk HBL) as BF.
          destruct (M3W y ltac:(unfold A_ERRNO, TPV in Hy; lia) NE) as [W|[W|W]];
            unfold UbMhAMetaT.ctxV, ctx_avail_meta_area_count, ctx_avail_meta_areas, ctx_brk, CTX, AMSTK, A_ERRNO, TPV in *; [lia | lia | clear -W BF Hy; lia].
        + left; reflexivity.
        + (* [comment removed for export] *) intros x Hx. split; [unfold HEAPLO; lia|]. split; [lia|]. split.
          * intros ar Har IN. destruct (area_in_region st L HWF ar Har) as (rr & Hrr & _ & Y1 & Y2). destruct (AP rr Hrr); lia.
          * intros t Ht Kt IN. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
            destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end in IN; lia.
        + intros x Hx. left. exists (UbMhAMetaR.c3_Rn bk). split; [left; reflexivity|]. unfold UbMhAMetaR.c3_Rn. cbn. split; [intros y E; discriminate E | lia].
        + (* [comment removed for export] *) intros x Hd D. unfold M3. repeat apply (wbytes_grows _ _ _ (Z_to_bv 64 x)). unfold M2. apply zfill_grows. exact (UbMhAMetaS.M1_grows st M regs sp _ D).
        + (* [comment removed for export] *) intros x Hx. unfold M3, ctx_brk, ctx_avail_meta_area_count, CTX. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
          unfold M2. apply zfill_inZ; lia.
        + unfold M3. repeat apply defined_wbytes. unfold M2. eapply defined_grows; [apply zfill_grows | exact (UbMhAMetaS.M1_def st M regs sp DEF)].
        + unfold cell, M3, ctx_brk, ctx_avail_meta_area_count, CTX. apply rdn_wbytes_hit8. zsimp; lia.
        + unfold cell, M3, ctx_brk, ctx_avail_meta_area_count, ctx_meta_alloc_shift, CTX in *. do 2 rdn_peel1. unfold M2. rewrite rdn_zfill_outZ by (cbn; lia). exact (rc_mas st M1 RC1).
        + unfold cell, M3, ctx_brk, ctx_avail_meta_area_count, CTX. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
        + lia.
        + exact (UbMhAMetaR.c3_Hp st L X _ HWF HLG b0 bk gk HBL Hce).
        + exact (UbMhAMetaR.c3_Hp_img st L X _ HWF HLG b0 bk gk HBL).
        + exact (UbMhAMetaR.c3_Hp_areas st L X _ HWF HLG XOK b0 bk gk HBL Hce HRF).
        + exact (UbMhAMetaR.c3_Hp_groups st L X _ HWF HLG XOK b0 bk gk HBL Hce HRF).
        + exact Hcnt.
        + exact (UbMhAMetaR.c3_HRgrp st bk).
        + exact (UbMhAMetaR.c3_HRsub st bk).
        + exact (UbMhAMetaR.c3_HRold st L HWF b0 bk gk HBL).
        + exact (UbMhAMetaR.c3_HRnew st L X _ HWF HLG b0 bk gk HBL).
        + intros HH. lia.
        + pose proof (UbMhAMetaR.c3_Hsh' st L HWF Hac) as HS. replace (1 - 1) with 0 by lia. exact HS.
        + pose proof (wc_shacc st (WF_ctx st L HWF)) as SA. clear -SA Hac. lia.
        + exact (UbMhAMetaR.c3_Hbrk' st L X _ HWF HLG b0 bk gk HBL Hce).
        + pose proof (UbMhAMetaR.c3_t_wf_regions st L X _ HWF HLG XOK b0 bk gk HBL Hce HRF) as WR.
          unfold UbMhAMetaR.c3_st, UbMhAMetaR.c3_p in WR. replace (1 - 1) with 0 by lia. exact WR.
        + pose proof (UbMhAMetaR.c3_t_wf_img st L X _ HWF HLG b0 bk gk HBL) as WI.
          unfold UbMhAMetaR.c3_st, UbMhAMetaR.c3_p in WI. replace (1 - 1) with 0 by lia. exact WI.
        + rewrite MF1. unfold brk_grow_vm. rewrite ?EB. rewrite (u_Z2bv bk) by lia.
          pose proof (UbMhAMetaR.c3_t_ledger st L X _ HWF HLG b0 bk gk HBL Hce) as LG.
          unfold UbMhAMetaR.c3_st, UbMhAMetaR.c3_vm, UbMhAMetaR.c3_p in LG. rewrite ?EB in LG. replace (1 - 1) with 0 by lia. exact LG.
        + rewrite (UbMhAMetaR.c3_RSUM st bk). lia.
        + rewrite (UbMhAMetaR.c3_len st bk). lia.
        + exact (UbMhAMetaR.c3_new_apart_X st L X _ HWF HLG XOK b0 bk gk HBL Hce HRF).
        + intros t Ht Kt. pose proof (wg_kind st L t (wG_each st L (WF_groups st L HWF) t Ht)) as KD2. rewrite Kt in KD2. destruct KD2 as (_ & Hin & _).
          destruct (AP _ Hin) as [DJ|DJ]; cbn in DJ; unfold g_map_end; lia.
        + intros x n bs Hx Hn R. unfold M3, ctx_brk, ctx_avail_meta_area_count, CTX. do 2 rdn_peel1. unfold M2. rewrite rdn_zfill_outZ by lia. exact R.
    Qed.
  End ArmC3.
End AMC.
