(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (imports Placement, AsanPlacement and AMark; aevtS_sys and spinningJ_sys take the sys_rob premise, discharged at each mmap and munmap call; anon_grantable written out with grant_placed, Linux's placement test and the ASan lower bound, in place of the bottom-up floor; aevtS_mmap_anon's grant continuation takes placed_at, its old encoded statement kept and proved equal to the new one without it; munmap may answer a refusal from munmap_errnos, with the new munmap_refusal_spurious and aevtS_munmap restated; the mmap checks unfold check_mmap_fixed_overflow and discharge place_declined_b at the NULL hint). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac ITree Nodes SysStep AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require SpinAlg.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
(* LPS #38: the anonymous arms of [Checks.Sys.Mm.Mmap.check_mmap] gate on
   [Placement.linux_place_is] -- the address IS the one Linux gives -- so the
   grant predicate carries that test and the lower bound the split ledger buys.
   [Require] without [Import]: [ABoot.AsanCeil] also defines [bottomup_floor],
   which would shadow [ACeil]'s. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require AsanPlacement.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require AMark.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ASysS () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.ITree.nret"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.LibA.SRz.spinningJ"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.AHeap.ACeil.bottomup_floor"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.AHeap.ACeil.ACEIL"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_backing_used"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "OSSVerify.KrLib.AHeap.ASys.mmap_anon_args"; "OSSVerify.KrLib.AHeap.ACeil.atop_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "ARUN_1.WithSegs.anon_grantable"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "OSSVerify.KrLib.AHeap.ASys.anon_grant"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.MState.MSsvc"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_budget_ok"; "OSSVerify.KrLib.AHeap.ASys.mmap_fixrw_args"; "ARUN_1.WithSegs.fixrw_grantable"; "OSSVerify.KrLib.AHeap.ASys.fixrw_outcome"; "OSSVerify.KrLib.Lib.ITree.resp"; "OSSVerify.KrLib.AHeap.ASys.mmap_norep_args"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM"; "LinuxProcessSemantics.LinuxProcessSem.State.EEXIST"; "OSSVerify.KrLib.AHeap.ASys.norep_grant"; "OSSVerify.KrLib.AHeap.ASys.munmap_args"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "OSSVerify.KrLib.AHeap.ASys.munmap_model"; "OSSVerify.KrLib.AHeap.ASys.madvise_args"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "OSSVerify.KrLib.AHeap.ASys.madvise_model"; "OSSVerify.KrLib.Lib.AEvt.aevt"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma aevtS_sys : forall (Q : config -> Prop) ms mo x8,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (exists eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) /\ syscall_effect_accesses eff = []
                   /\ aevtS segs Q (mkCfg (nret ms eff) mo')) ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
      evs = [] /\ m_halted mo' = None /\ syscall_effect_accesses eff = []
      /\ (aevtS segs Q (mkCfg (nret ms eff) mo')
          \/ (spinningJ segs (mkCfg (nret ms eff) mo') /\ spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) mo eff))) ->
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) ->
  RomBase.sys_rob segs (mkCfg ms mo) ->
  aevtS segs Q (mkCfg ms mo).
(* [comment removed for export] *)
Proof.
  (intros Q ms mo x8 Hsvc Hh dd_H; ddestruct dd_H as (effw & mow & Hsw & Haccw & HQw); intros HQ HU Hrob).
  apply aevtS_step.
  - exists (mkCfg (nret ms effw) mow). split; [| exact HQw].
    destruct (HQ _ _ _ Hsw) as (_ & Hh' & _ & _).
    unfold nret. eapply sstep_syscall; eauto. rewrite Haccw. apply materialize_nil.
  - intros e st Hs. destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hs)
      as [(eff & mo' & mo'' & Hsp & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hsp & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & ->) | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
    + destruct (HQ _ _ _ Hsp) as (-> & _). split; [reflexivity| discriminate].
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & _ & Hacc & _). rewrite Hacc, materialize_nil in Hm. discriminate.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). congruence.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
    + exfalso. exact (HU Hsp).
  - intros e c' Hs. destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hs)
      as [(eff & mo' & mo'' & Hsp & Hh' & Hm & E) | [(eff & mo' & evs0 & Hsp & Hh' & Hm & -> & E) | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & E) | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & E) | (Hsp & -> & E)]]]];
      try discriminate.
    + destruct (HQ _ _ _ Hsp) as (-> & _ & Hacc & HQ'). rewrite Hacc, materialize_nil in Hm.
      inversion Hm; subst. inversion E; subst.
      destruct HQ' as [A | [SP SR]]; [left; exact A | right]. split; [exact SP|].
      eapply spurious_fo_excusedJ; [exact Hsvc | exact SR].
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). congruence.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
  - exact Hrob.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_refusal_spurious : forall ms x8 mo effg mog evsg eff,
  bv_unsigned x8 = 222 ->
  syscall_spec (sys_input segs ms x8) mo (Ok effg mog evsg) ->
  errno_ret_in mmap_errnos (eff_ret effg) = false ->
  errno_ret_in mmap_errnos (eff_ret eff) = true ->
  spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) mo eff.
Proof.
  intros ms x8 mo effg mog evsg eff Hno Hsg NR R.
  assert (E8 : bv_unsigned (in_sysno (sys_input segs ms x8)) = 222) by (cbn [in_sysno sys_input]; exact Hno).
  split; [apply SpinAlg.family_off_alloc; rewrite E8; right; right; left; reflexivity|].
  split; [rewrite (SpinAlg.refusal_b_mmap _ mo _ E8); exact R|].
  exists effg, mog, evsg. split; [exact Hsg|]. rewrite (SpinAlg.refusal_b_mmap _ mo _ E8). exact NR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma grant_ret_not_errno : forall (a : word) nZ, 0 <= nZ -> bv_unsigned a + nZ <= ACEIL ->
  errno_ret_in mmap_errnos a = false.
Proof.
  intros a nZ Hn CE. aceilb. apply errno_ret_in_below; [reflexivity|]. unfold two_pow_64. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* WHAT REPLACED THE FLOOR, AND WHY.  The third conjunct was
   [bottomup_floor <= bv_unsigned a].  Revision #38 makes that FALSE for some
   admissible kernels: [check_mmap]'s modeled-anon arm
   ([Checks/Sys/Mm/Mmap.v:111]) now gates on [Placement.linux_place_is], and
   Linux's NULL-hint answer is top-down below [mmap_top h], which
   [Run.valid_mmap_base] ([Run.v:3154]) allows down to
   [State.mmap_base_min = 0x154555557000] -- BELOW
   [bottomup_floor = 0x2aaaaaaab000].  So the grant can land under the floor.

   [grant_placed] is the replacement, and it occupies the SAME SLOT: the
   checker's own test, plus the lower bound that [AMark.heap_mark_place]
   derives from the split ledger, which is what the floor conjunct was really
   carrying for the ASan layer ([kHighMemBeg] is the end of the high shadow,
   so every application address must exceed it).  Keeping it in one slot keeps
   [anon_grantable] at six conjuncts, so every
   [ddestruct ... as (AL & A0 & FL & CE & RF & BU)] in the tree still binds six
   names and the thirty opaque [exists a, anon_grantable ...] uses are
   untouched.

   [kb_thp] IS NOT PINNED: it is read off the run's own model, never assumed.
   It is one of the five fields [Run.recorded_kernel] ([Run.v:4575-4581])
   leaves free.

   Written as explicit text rather than re-encoded: the KReplay rule forbids
   decoding and re-encoding a [CDefT.buildp] blob, so the blob is replaced. *)
Definition grant_placed (nZ : Z) (mo : Model) (a : word) : Prop :=
  Placement.linux_place_is (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nZ a = true
  /\ AsanPlacement.kHighMemBeg < bv_unsigned a.

Definition anon_grantable (flags nZ : Z) (mo : Model) (a : word) : Prop :=
  bv_unsigned a mod 4096 = 0
  /\ 0 < bv_unsigned a
  /\ grant_placed nZ mo a
  /\ bv_unsigned a + nZ <= ACEIL
  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true
  /\ (flags = 34 -> vm_backing_used mo + nZ <= vm_limit (m_vmmaps mo)).


(* [comment removed for export] *)
#[using="Type"] Lemma mmap_anon_grant_spec : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.PnZ,$1=.Pflags,$1=.Pa,(3.&40.)P,(4.$1=.(1?.&40.R5.)+=>.)P,(2?.R7.R4.R3.)P,(30.VhAR,(31.(29.R6.)))P,(32.R5.R6.R7.R4.)(=.(>.Vsegs,R:.R9.)R8.(?.$;.(33.R5.(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)R5.(2;.&40.R7.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.)))(37.R6.R5.R7.R8.)(10.$11.)))")
(* [comment removed for export] *).
Proof.
  (intros ms x8 mo nZ flags a Hno HA ATOP dd_H; ddestruct dd_H as (AL & A0 & FL & CE & RF & BU)). aceilb.
  dpose (anon_gates ms nZ flags HA) as (Ga & Gb & G0 & G1).
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & N0 & FOK).
  apply check_syscall_ok_iff. rewrite (mmap_check segs ms x8 mo _ Hno).
  unfold check_mmap, check_mmap_fixed_overflow. rewrite Ga, Gb, G0, G1. cbn [negb]. cbv zeta.
  (* LPS 727298f3: the call's hint is NULL ([H10]), which no decline holds of *)
  lazymatch goal with |- context [place_declined_b ?dk ?dh ?da ?dn] =>
    replace (place_declined_b dk dh da dn) with false
      by (rewrite (H10 : da = Z_to_bv 64 0); reflexivity) end.
  rewrite Hn, H13. cbv beta iota.
  rewrite (errno_ret_in_below mmap_errnos a) by (first [reflexivity | unfold two_pow_64; lia]).
  (* #38: the modeled-anon arm's gate is ONE test, [Placement.linux_place_is],
     and the four conditions the old guard listed are its consequences
     ([Placement.linux_place_is_admissible]) rather than separate checks.  So
     the four rewrites that discharged them are gone and [H10] -- the call's
     NULL a0 -- lines the gate's hint up with [grant_placed]'s. *)
  rewrite H10, (proj1 FL).
  assert (NR : mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo nZ = true).
  { unfold mmap_noreserve_backed_ok. destruct FOK as [-> | ->].
    - replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity). apply Z.leb_le. apply BU. reflexivity.
    - replace (mmap_noreserve_b (Z_to_bv 64 16418)) with true by (vm_compute; reflexivity). reflexivity. }
  rewrite NR. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb]. reflexivity.
Qed.

(* [comment removed for export] *)
(** THE GRANT CONTINUATION GAINS THE PLACEMENT.

    [AO_grant] now carries [ASys.placed_at] (the gate the checker tested), and
    the whole point of carrying it is that the continuation below -- whose [a]
    comes out of the INVERSION, not out of [anon_grantable] -- can see it.  So
    the fifth argument gains one premise, in [AO_grant]'s own order.

    The [CDefT] blob is REPLACED by explicit text rather than decoded and
    re-encoded (rule 4).  [ZZ_aevtS_mmap_anon_old] keeps the old blob verbatim
    and [ZZ_aevtS_mmap_anon_faithful] makes the compiler certify that the text
    below, MINUS the new premise, is the old statement on the nose -- so a
    transcription slip is a build error, not a silent weakening.  The probe is
    inline because [ZZ_*] files are gitignored here and would be dropped from
    the [git archive] the farm builds. *)
Definition ZZ_aevtS_mmap_anon_old : Prop := ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PQ,P,$0.SpPR,(38.&5.(3.&40.))PF,(38.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.PnZ,$1=.Pflags,$1=.Zms,$1.(39.R9.R8.R7.(2;.&40.+=>.)R6.R5.R4.(3:.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(30.VhAR,(31.(29.R5.)))P,(2?.R3.R5.R4.)P,(:.(3.&40.)La,(3.&40.)(32.R6.R7.R8.R1.))P,Pe,$1=.P,(3;.$1=.R1.$3<.)(19.(16.Vsegs,R11.(17.(18.R7.(33.(3=.R2.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R:.))(1:.Vsegs,(17.(18.R7.(33.(3=.R2.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R:.)))P,Pa,(3.&40.)P,(4.$1=.(1>.(1?.&40.R1.)+1000.)=)P,(20.=(1?.&40.R2.))P,(21.(23.(1?.&40.R3.)R;.)(24.VhAR,))P,(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R=.))(2:.(29.R=.)))R4.(2;.&40.R<.))$2<.)(16.Vsegs,R15.(17.(18.R;.(33.R5.(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)R5.(2;.&40.R=.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))(37.R<.R5.R=.R>.)))(16.Vsegs,R11.(17.R7.R:.))").

Lemma ZZ_aevtS_mmap_anon_faithful : ZZ_aevtS_mmap_anon_old =
  (forall (Q : config -> Prop) (R F : bvmap 5 word) (pc : word) (fc : bv 32)
          (rv : option word) (m : word -> option (bv 8)) (mo : Model) (nZ flags : Z),
     let ms : machine_state := MSsvc R F pc (Z_to_bv 64 222) fc rv m (seg_rom segs) in
     m_halted mo = None ->
     atop_ok (alloc_top (m_vmmaps mo)) ->
     mmap_anon_args ms nZ flags ->
     (exists a : word, anon_grantable flags nZ mo a) ->
     (forall e : Z,
        In e mmap_errnos ->
        aevtS segs Q (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo)
        \/ spinningJ segs (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo)) ->
     (forall a : word,
        bv_unsigned a mod 4096 = 0 ->
        0 < bv_unsigned a ->
        bv_unsigned a + nZ <= ACEIL ->
        region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true ->
        aevtS segs Q (mkCfg (nret ms (mkEffect a [] [(a, Z_to_bv 64 nZ)])) (anon_grant flags a nZ mo))) ->
     aevtS segs Q (mkCfg ms mo)).
Proof. exact eq_refl. Qed.

#[using="Type"] Lemma aevtS_mmap_anon :
  forall (Q : config -> Prop) (R F : bvmap 5 word) (pc : word) (fc : bv 32)
         (rv : option word) (m : word -> option (bv 8)) (mo : Model) (nZ flags : Z),
    let ms : machine_state := MSsvc R F pc (Z_to_bv 64 222) fc rv m (seg_rom segs) in
    m_halted mo = None ->
    atop_ok (alloc_top (m_vmmaps mo)) ->
    mmap_anon_args ms nZ flags ->
    (exists a : word, anon_grantable flags nZ mo a) ->
    (forall e : Z,
       In e mmap_errnos ->
       aevtS segs Q (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo)
       \/ spinningJ segs (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo)) ->
    (forall a : word,
       bv_unsigned a mod 4096 = 0 ->
       0 < bv_unsigned a ->
       placed_at nZ mo a ->
       bv_unsigned a + nZ <= ACEIL ->
       region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true ->
       aevtS segs Q (mkCfg (nret ms (mkEffect a [] [(a, Z_to_bv 64 nZ)])) (anon_grant flags a nZ mo))) ->
    aevtS segs Q (mkCfg ms mo).
Proof.
  intros Q R F pc fc rv m mo nZ flags ms Hh ATOP HA (aw & GW) HR HG.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  pose proof (mmap_anon_grant_spec ms (Z_to_bv 64 222) mo nZ flags aw E222 HA ATOP GW) as Hsg.
  assert (NRg : errno_ret_in mmap_errnos (eff_ret (mkEffect aw [] [(aw, Z_to_bv 64 nZ)])) = false).
  { cbn [eff_ret]. ddestruct GW as (AL & A0 & FL & CE & RF & BU). dpose HA as (_ & _ & _ & _ & _ & _ & _ & N0 & _).
    apply (grant_ret_not_errno aw nZ); lia. }
  eapply aevtS_sys with (x8 := Z_to_bv 64 222);
    [reflexivity| exact Hh| | |
    | eapply (RomBase.sys_rob_memfree segs); [reflexivity | exact RomBase.memfree_222]].
  - dexists (mkEffect aw [] [(aw, Z_to_bv 64 nZ)]), (anon_grant flags aw nZ mo).
    split; [exact Hsg|]. split; [reflexivity|].
    (* [FL] IS the new premise: [placed_at nZ mo aw] is convertible with
       [grant_placed]'s first conjunct, so [proj1 FL] discharges it. *)
    ddestruct GW as (AL & A0 & FL & CE & RF & BU).
    apply HG; first [exact (proj1 FL) | assumption].
  - intros eff mo' evs Hs.
    destruct (mmap_anon_inv segs ms (Z_to_bv 64 222) mo nZ flags eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    (* one more name: [AO_grant]'s placement *)
    split; [reflexivity|]. destruct OUT as [e HIn | a AL A0 PL CE RF].
    + split; [exact Hh|]. split; [reflexivity|].
      destruct (HR e HIn) as [A | SP]; [left; exact A | right]. split; [exact SP|].
      apply (mmap_refusal_spurious ms (Z_to_bv 64 222) mo _ _ _ _ E222 Hsg NRg). cbn [eff_ret]. apply errno_ret_in_intro. exact HIn.
    + split; [rewrite halted_anon_grant; exact Hh|]. split; [reflexivity|]. left. apply HG; assumption.
  - eapply (mmap_anon_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixrw_grantable (flags addr nZ : Z) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "(<.P,(4.$25.(3>.(2:.(29.O1.))(2;.&40.O3.)(2;.&40.O2.))$2<.)(4.$25.(3?.(2;.&40.O4.)O1.(2;.&40.O3.)(2;.&40.O2.))$2<.)P,(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.O1.))(2:.(29.O1.)))(2;.&40.O3.)(2;.&40.O2.))$2<.)P,(4.$1=.O4.+32.)(21.(23.(2=.O1.)O2.)(2>.(29.O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixrw_grant_spec : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1=.PnZ,$1=.Pflags,$1=.P,(4.$1=.(1?.&40.R5.)+=>.)P,(40.VhAR,R7.R4.R3.R2.)P,(30.VhAR,(31.(29.R6.)))P,(4.$25.(26.(28.(29.R7.))(2;.&40.R6.)(2;.&40.R5.))$2<.)P,(19.(4.$25.(3>.(2:.(29.R8.))(2;.&40.R7.)(2;.&40.R6.))$2<.)(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R8.))(2:.(29.R8.)))(2;.&40.R7.)(2;.&40.R6.))$2<.))P,(41.R6.R8.R7.R9.)(:.$2.Lmo',$2.(<.(42.R8.R:.R9.R;.(33.(2;.&40.R:.)(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R:.)(2;.&40.R9.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.)))R1.)(<.(4.(5.(3.&40.))(8.R1.)(8.R;.))(=.(>.Vsegs,R=.R<.)R;.(?.$;.(33.(2;.&40.R:.)(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R:.)(2;.&40.R9.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.)))R1.(10.$11.))))))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ flags Hno HA ATOP RF CASES [GC GF]. aceilb.
  dpose (fixrw_gates ms addr nZ flags HA) as (Ga & Gb & G0 & G1 & G2 & G3 & G4).
  dpose HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE & FL).
  assert (ER : errno_ret_in mmap_errnos (Z_to_bv 64 addr) = false).
  { apply errno_ret_in_below; [reflexivity|]. rewrite unsigned_lit by lia. unfold two_pow_64. lia. }
  assert (PREP : forall res,
    check_mmap (areg ms 10) (areg ms 11) (areg ms 12) (areg ms 13) (areg ms 14) (areg ms 15)
               (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) mo = res ->
    check_syscall (sys_input segs ms x8) (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) mo = res).
  { intros res <-. apply (mmap_check segs _ _ _ _ Hno). }
  destruct (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:MC.
  - exists (fixrw_commit flags addr nZ mo). split; [apply FO_commit; exact MC|]. split; [apply halted_fixrw_commit|].
    apply check_syscall_ok_iff. apply PREP.
    unfold check_mmap, check_mmap_fixed_overflow. rewrite Ga, Gb, G0, G1, G2, G3, G4. cbn [negb]. cbv zeta.
    rewrite H10. rewrite !unsigned_lit by lia. rewrite Hn.
    destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|].
    destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]. cbn [negb].
    change page_size with 4096. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
    destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]. cbn [negb].
    rewrite RF, MC. cbn [andb]. cbv beta iota.
    rewrite ER. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). rewrite H13, (GC eq_refl). cbn [andb].
    unfold fixrw_commit. reflexivity.
  - destruct CASES as [MC'|FR]; [congruence|].
    exists (fixrw_fresh flags addr nZ mo). split; [apply FO_fresh; exact FR|]. split; [apply halted_fixrw_fresh|].
    apply check_syscall_ok_iff. apply PREP.
    unfold check_mmap, check_mmap_fixed_overflow. rewrite Ga, Gb, G0, G1, G2, G3, G4. cbn [negb]. cbv zeta.
    rewrite H10. rewrite !unsigned_lit by lia. rewrite Hn.
    destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|].
    destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]. cbn [negb].
    change page_size with 4096. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
    destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]. cbn [negb].
    rewrite RF, MC. cbn [andb]. rewrite FR. cbv beta iota.
    rewrite ER. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). rewrite H13.
    assert (NR : mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo nZ = true).
    { unfold mmap_noreserve_backed_ok. destruct FL as [-> | ->].
      - replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity). apply Z.leb_le. apply GF; [exact FR| reflexivity].
      - replace (mmap_noreserve_b (Z_to_bv 64 16434)) with true by (vm_compute; reflexivity). reflexivity. }
    rewrite NR. cbn [andb]. unfold fixrw_fresh. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_mmap_fixrw : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PQ,P,$0.SpPR,(38.&5.(3.&40.))PF,(38.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.Paddr,$1=.PnZ,$1=.Pflags,$1=.Zms,$1.(39.R:.R9.R8.(2;.&40.+=>.)R7.R6.R5.(3:.Vsegs,))P,(4.(5.(3.&40.))(8.R5.)(9.(3.&40.)))P,(30.VhAR,(31.(29.R6.)))P,(40.VhAR,R3.R6.R5.R4.)P,(4.$25.(26.(28.(29.R8.))(2;.&40.R7.)(2;.&40.R6.))$2<.)P,(19.(4.$25.(3>.(2:.(29.R9.))(2;.&40.R8.)(2;.&40.R7.))$2<.)(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R9.))(2:.(29.R9.)))(2;.&40.R8.)(2;.&40.R7.))$2<.))P,(41.R7.R9.R8.R:.)P,Pmo',$2.P,(42.R9.R;.R:.R<.(33.(2;.&40.R;.)(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R;.)(2;.&40.R:.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.)))R1.)(16.Vsegs,R14.(17.(18.R9.(33.(2;.&40.R<.)(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R<.)(2;.&40.R;.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R2.))P,Peff,$43.Pmo',$2.P,(42.R;.R=.R<.R>.R2.R1.)(19.(16.Vsegs,R16.(17.(18.R;.R3.)R2.))(1:.Vsegs,(17.(18.R;.R3.)R2.)))(16.Vsegs,R14.(17.R9.R=.))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo addr nZ flags ms Hh ATOP HA RF CASES GR HOK HALL.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  ddestruct (mmap_fixrw_grant_spec ms (Z_to_bv 64 222) mo addr nZ flags E222 HA ATOP RF CASES GR) as (mog & OUTg & Hhg & Hsg).
  assert (NRg : errno_ret_in mmap_errnos (eff_ret (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) = false).
  { cbn [eff_ret]. dpose HA as (_ & _ & _ & _ & _ & _ & _ & AL & A0 & N0 & CE & _). aceilb.
    apply (grant_ret_not_errno (Z_to_bv 64 addr) nZ); [lia|]. rewrite unsigned_lit by lia. exact CE. }
  assert (SPUR : forall e w z u c i, In e mmap_errnos ->
            spurious_refusal_cfg forced_only_cfg (sys_input segs ms (Z_to_bv 64 222)) mo (mkEffectU (errno_ret e) w z u c i)).
  { intros e w z u c i HIn. apply (mmap_refusal_spurious ms (Z_to_bv 64 222) mo _ _ _ _ E222 Hsg NRg). cbn [eff_ret].
    apply errno_ret_in_intro. exact HIn. }
  eapply aevtS_sys with (x8 := Z_to_bv 64 222);
    [reflexivity| exact Hh| | |
    | eapply (RomBase.sys_rob_memfree segs); [reflexivity | exact RomBase.memfree_222]].
  - dexists (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]), mog.
    split; [exact Hsg|]. split; [reflexivity|]. apply HOK. exact OUTg.
  - intros eff mo' evs Hs.
    destruct (mmap_fixrw_inv segs ms (Z_to_bv 64 222) mo addr nZ flags eff mo' evs E222 HA ATOP RF CASES Hs) as [-> OUT].
    split; [reflexivity|]. pose proof OUT as OUT'. destruct OUT as [e HIn | e HIn MC | MC | FR'].
    + (* [comment removed for export] *)
      split; [exact Hh|]. split; [reflexivity|].
      destruct (HALL _ _ OUT') as [A | SP]; [left; exact A | right]. split; [exact SP| apply SPUR; exact HIn].
    + (* [comment removed for export] *)
      split; [rewrite halted_fixrw_destroyed; exact Hh|]. split; [reflexivity|].
      destruct (HALL _ _ OUT') as [A | SP]; [left; exact A | right]. split; [exact SP| apply SPUR; exact HIn].
    + (* [comment removed for export] *)
      split; [rewrite halted_fixrw_commit; exact Hh|]. split; [reflexivity|]. left. apply HOK. exact OUT'.
    + (* [comment removed for export] *)
      split; [rewrite halted_fixrw_fresh; exact Hh|]. split; [reflexivity|]. left. apply HOK. exact OUT'.
  - eapply (mmap_fixrw_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* Was an encoded statement (CDefT.buildp); written out from its decode (cdeft_print.py), not
   re-encoded, with one premise added: [RomBase.sys_rob segs (mkCfg ms mo)], which
   [SRz.spinningJ_node] now asks for.  Its three callers (here and A|BHeap/AKinvM) are at
   x8 = 222 and discharge it by [RomBase.sys_rob_memfree]. *)
#[using="Type"] Lemma spinningJ_sys : forall (ms : machine_state) (mo : Model) (x8 : bv 64),
  ms_svc_pending ms = Some x8 ->
  m_halted mo = None ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     evs = [] /\ m_halted mo' = None /\ syscall_effect_accesses eff = []
     /\ spinningJ segs (mkCfg (nret ms eff) mo')) ->
  ~ syscall_spec (sys_input segs ms x8) mo Unmodeled ->
  RomBase.sys_rob segs (mkCfg ms mo) ->
  spinningJ segs (mkCfg ms mo).
Proof.
  intros ms mo x8 Hsvc Hh HQ HU Hrob.
  assert (PROG : exists eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)).
  { pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    - dexists eff, mo', evs. exact Hr.
    - exfalso. exact (HU Hr). }
  apply spinningJ_node; [exact Hh| | |exact Hrob].
  - ddestruct PROG as (eff & mo' & evs & Hs). destruct (HQ _ _ _ Hs) as (-> & Hh' & Hacc & _).
    dexists [], (SNext (mkCfg (nret ms eff) mo')). unfold nret. eapply sstep_syscall; eauto.
    rewrite Hacc. apply materialize_nil.
  - intros e st Hs. destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hs)
      as [(eff & mo' & mo'' & Hsp & Hh' & Hm & E) | [(eff & mo' & evs0 & Hsp & Hh' & Hm & -> & E) | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & E) | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & E) | (Hsp & -> & E)]]]].
    + destruct (HQ _ _ _ Hsp) as (-> & _ & Hacc & SP). rewrite Hacc, materialize_nil in Hm. inversion Hm; subst.
      split; [reflexivity|]. eexists. split; [reflexivity| exact SP].
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & _ & Hacc & _). rewrite Hacc, materialize_nil in Hm. discriminate.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). congruence.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
    + exfalso. exact (HU Hsp).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma spinningJ_mmap_norep_live : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PR,(38.&5.(3.&40.))PF,(38.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.Paddr,$1=.PnZ,$1=.Zms,$1.(39.R9.R8.R7.(2;.&40.+=>.)R6.R5.R4.(3:.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(30.VhAR,(31.(29.R5.)))P,(44.VhAR,R3.R5.R4.)P,(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R7.))(2:.(29.R7.)))(2;.&40.R6.)(2;.&40.R5.))$45.)P,Pe,$1=.P,(19.(4.$1=.R1.$46.)(4.$1=.R1.$47.))(1:.Vsegs,(17.(18.R7.(33.(3=.R2.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R:.))(1:.Vsegs,(17.R6.R9.))")
(* [comment removed for export] *).
Proof.
  intros R F pc fc rv m mo addr nZ ms Hh ATOP HA OCC HSP.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  eapply spinningJ_sys with (x8 := Z_to_bv 64 222);
    [reflexivity| exact Hh| |
    | eapply (RomBase.sys_rob_memfree segs); [reflexivity | exact RomBase.memfree_222]].
  - intros eff mo' evs Hs.
    destruct (mmap_norep_inv segs ms (Z_to_bv 64 222) mo addr nZ eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    split; [reflexivity|]. destruct OUT as [| _ | FR].
    + split; [exact Hh|]. split; [reflexivity|]. apply HSP. left. reflexivity.
    + split; [exact Hh|]. split; [reflexivity|]. apply HSP. right. reflexivity.
    + congruence.
  - eapply (mmap_norep_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_norep_grant_spec : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1=.PnZ,$1=.P,(4.$1=.(1?.&40.R4.)+=>.)P,(44.VhAR,R6.R3.R2.)P,(30.VhAR,(31.(29.R5.)))P,(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R6.))(2:.(29.R6.)))(2;.&40.R5.)(2;.&40.R4.))$2<.)(=.(>.Vsegs,R9.R8.)R7.(?.$;.(33.(2;.&40.R6.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R6.)(2;.&40.R5.))(10.(13.(3.&40.)(3.&40.))))(10.$36.)(10.(13.(3.&40.)$14.)))(48.R6.R5.R7.)(10.$11.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ Hno HA ATOP FR. aceilb.
  dpose (norep_gates ms addr nZ HA) as (Ga & Gb & G0 & G1 & G2 & G3 & G4 & G5).
  dpose HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE).
  assert (ER : errno_ret_in mmap_errnos (Z_to_bv 64 addr) = false).
  { apply errno_ret_in_below; [reflexivity|]. rewrite unsigned_lit by lia. unfold two_pow_64. lia. }
  apply check_syscall_ok_iff. rewrite (mmap_check segs _ _ _ _ Hno).
  unfold check_mmap, check_mmap_fixed_overflow. rewrite Ga, Gb, G0, G1, G2, G3, G4, G5. cbn [negb]. cbv zeta.
  rewrite H10. rewrite !unsigned_lit by lia. rewrite Hn.
  destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|].
  destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]. cbn [negb].
  change page_size with 4096. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
  destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]. cbn [negb].
  rewrite FR. cbv beta iota.
  rewrite ER. rewrite bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb]. rewrite H13.
  unfold norep_grant. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_mmap_norep_hole : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PQ,P,$0.SpPR,(38.&5.(3.&40.))PF,(38.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.Paddr,$1=.PnZ,$1=.Zms,$1.(39.R9.R8.R7.(2;.&40.+=>.)R6.R5.R4.(3:.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(30.VhAR,(31.(29.R5.)))P,(44.VhAR,R3.R5.R4.)P,(4.$25.(26.(27.(13.(3.&40.)(3.&40.))(28.(29.R7.))(2:.(29.R7.)))(2;.&40.R6.)(2;.&40.R5.))$2<.)P,(16.Vsegs,R?.(17.(18.R5.(33.(2;.&40.R7.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R7.)(2;.&40.R6.))(10.(13.(3.&40.)(3.&40.))))(10.$36.)(10.(13.(3.&40.)$14.))))(48.R7.R6.R8.)))P,(19.(16.Vsegs,R10.(17.(18.R6.(33.(3=.$46.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R9.))(1:.Vsegs,(17.(18.R6.(33.(3=.$46.)(10.(13.(3.&40.)(12.(3.&8.))))(10.(13.(3.&40.)(3.&40.)))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))R9.)))(16.Vsegs,R11.(17.R7.R:.))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo addr nZ ms Hh ATOP HA FR HOK HNO.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  pose proof (mmap_norep_grant_spec ms (Z_to_bv 64 222) mo addr nZ E222 HA ATOP FR) as Hsg.
  assert (NRg : errno_ret_in mmap_errnos (eff_ret (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [])) = false).
  { cbn [eff_ret]. dpose HA as (_ & _ & _ & _ & _ & _ & _ & AL & A0 & N0 & CE). aceilb.
    apply (grant_ret_not_errno (Z_to_bv 64 addr) nZ); [lia|]. rewrite unsigned_lit by lia. exact CE. }
  eapply aevtS_sys with (x8 := Z_to_bv 64 222);
    [reflexivity| exact Hh| | |
    | eapply (RomBase.sys_rob_memfree segs); [reflexivity | exact RomBase.memfree_222]].
  - dexists (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []), (norep_grant addr nZ mo).
    split; [exact Hsg|]. split; [reflexivity| exact HOK].
  - intros eff mo' evs Hs.
    destruct (mmap_norep_inv segs ms (Z_to_bv 64 222) mo addr nZ eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    split; [reflexivity|]. destruct OUT as [| OCC | _].
    + split; [exact Hh|]. split; [reflexivity|].
      destruct HNO as [A | SP]; [left; exact A | right]. split; [exact SP|].
      apply (mmap_refusal_spurious ms (Z_to_bv 64 222) mo _ _ _ _ E222 Hsg NRg). cbn [eff_ret]. apply errno_ret_in_intro. left. reflexivity.
    + congruence.
    + split; [rewrite halted_norep_grant; exact Hh|]. split; [reflexivity|]. left. exact HOK.
  - eapply (mmap_norep_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* 08b1429: munmap of an exact mapping may also answer an injected munmap_errnos
   refusal ([Mmap.munmap_spec]).  Under forced_only_cfg that refusal is spurious (the
   success outcome is admitted at the same input and model). *)
#[using="Type"] Lemma munmap_refusal_spurious : forall ms x8 mo effg mog evsg eff,
  bv_unsigned x8 = 215 ->
  syscall_spec (sys_input segs ms x8) mo (Ok effg mog evsg) ->
  errno_ret_in munmap_errnos (eff_ret effg) = false ->
  errno_ret_in munmap_errnos (eff_ret eff) = true ->
  spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) mo eff.
Proof.
  intros ms x8 mo effg mog evsg eff Hno Hsg NR R.
  assert (E8 : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215) by (cbn [in_sysno sys_input]; exact Hno).
  assert (RB : forall r, refusal_b (sys_input segs ms x8) mo r = errno_ret_in munmap_errnos r)
    by (intros r; unfold refusal_b; rewrite E8; reflexivity).
  split; [unfold injected_family_off; rewrite E8; reflexivity|].
  split; [rewrite RB; exact R|].
  exists effg, mog, evsg. split; [exact Hsg|]. rewrite RB. exact NR.
Qed.

(* 08b1429: the refused outcome is a real successor, so the caller now also shows that
   the refused configuration spins (ASan's UnmapOrDie reaches
   ReportMunmapFailureAndDie, whose gate executes [j .]); the success outcome is as
   before.  Plain text: the pre-revision statement had a single successor. *)
#[using="Type"] Lemma aevtS_munmap : forall (Q : config -> Prop) R F pc fc rv m mo addr nZ,
  let ms := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.MState.MSsvc R F pc (Z_to_bv 64 215) fc rv m
              (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib.PropExec.seg_rom segs) in
  m_halted mo = None ->
  munmap_args ms addr nZ ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  (forall e, In e munmap_errnos ->
     spinningJ segs (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo)) ->
  Q (mkCfg (nret ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []))
           (munmap_model addr nZ mo)) ->
  aevtS segs Q (mkCfg ms mo).
Proof.
  intros Q R F pc fc rv m mo addr nZ ms Hh HA MH HSP HQ.
  assert (E215 : bv_unsigned (Z_to_bv 64 215) = 215) by (vm_compute; reflexivity).
  pose proof (munmap_grant_spec segs ms (Z_to_bv 64 215) mo addr nZ E215 HA MH) as Hsg.
  assert (NRg : errno_ret_in munmap_errnos (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
  eapply aevtS_sys with (x8 := Z_to_bv 64 215);
    [reflexivity| exact Hh| | |
    | eapply (RomBase.sys_rob_memfree segs); [reflexivity | exact RomBase.memfree_215]].
  - dexists (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []), (munmap_model addr nZ mo).
    split; [exact Hsg|]. split; [reflexivity|]. apply aevtS_now. exact HQ.
  - intros eff mo' evs Hs.
    destruct (munmap_inv segs ms (Z_to_bv 64 215) mo addr nZ eff mo' evs E215 HA MH Hs)
      as [-> [(ER & Eeff & ->) | (-> & ->)]].
    + split; [reflexivity|]. split; [exact Hh|]. split; [rewrite Eeff; reflexivity|].
      right. split.
      * apply errno_ret_in_true in ER. destruct ER as (e & HIn & Er).
        rewrite Eeff, Er. exact (HSP e HIn).
      * exact (munmap_refusal_spurious ms (Z_to_bv 64 215) mo _ _ _ eff E215 Hsg NRg ER).
    + split; [reflexivity|]. split; [rewrite halted_munmap_model; exact Hh|]. split; [reflexivity|].
      left. apply aevtS_now. exact HQ.
  - eapply (munmap_no_unmodeled segs ms (Z_to_bv 64 215)); eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma aevtS_madvise : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PQ,P,$0.SpPR,(38.&5.(3.&40.))PF,(38.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.Paddr,$1=.PnZ,$1=.Zms,$1.(39.R9.R8.R7.(2;.&40.+>9.)R6.R5.R4.(3:.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(4<.R2.R4.R3.)P,(4.$25.(4=.(29.R6.)(2;.&40.R5.)(2;.&40.R4.))$2<.)P,(16.Vsegs,R>.(17.(18.R4.(33.(2;.&40.=)(10.(13.(3.&40.)(12.(3.&8.))))(34.(13.(3.&40.)(3.&40.))(35.(3.&40.)(3.&40.)(2;.&40.R6.)(2;.&40.R5.))(10.(13.(3.&40.)(3.&40.))))(10.(13.(3.&40.)(3.&40.)))(10.$36.)(10.(13.(3.&40.)$14.))))(4>.R6.R5.R7.)))(16.Vsegs,R?.(17.R5.R8.))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo addr nZ ms Hh HA OKG HQ.
  eapply aevtS_bind.
  - apply aevtS_of_aevt. eapply (aevt_madvise segs (fun c => c = mkCfg (nret ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) (madvise_model addr nZ mo)));
      [exact Hh| exact HA| exact OKG| reflexivity].
  - intros c' ->. exact HQ.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aevtS_of_aevt_bind : ltac2:(CDefT.buildp (gd_tbl_ASysS ()) "PP,P,$0.SpPQ,P,$0.SpPc,$0.P,(4?.Vsegs,R3.R1.)P,Pc',$0.P,A1.R5.R1.(16.Vsegs,R5.R2.)(16.Vsegs,R4.R3.)")
(* [comment removed for export] *).
Proof. intros P Q c H K. eapply aevtS_bind; [apply aevtS_of_aevt; exact H| exact K]. Qed.

End WithSegs.

End ARUN_1.
