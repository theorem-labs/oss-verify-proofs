(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (Placement and RomBase imported; aevt_sys written out in plain text with the new premise RomBase.sys_rob, which the mmap and madvise steps discharge; placed_at added, the checker's linux_place_is test, and required by AO_grant; the mmap proofs read the placement and its admissibility facts, rule out place_declined_b for a NULL hint and unfold the new MAP_FIXED overflow check; munmap_model and munmap_inv written out in plain text, munmap_inv with the injected-refusal outcome; munmap_grant_spec added; aevt_munmap removed). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Placement.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac ITree Nodes SysStep AEvt.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require RomBase.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.

From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ASys () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.Lib.ITree.nret"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "OSSVerify.KrLib.Lib.AEvt.aevt"; "OSSVerify.KrLib.Lib.Nodes.areg"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.AHeap.ACeil.ACEIL"; "ARUN_1.WithSegs.fix_flags_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_replacement"; "LinuxProcessSemantics.LinuxProcessSem.State.with_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_next"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_destroyed"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_destroyed_next"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.with_mmap_backing"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.check_syscall"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_mmap"; "ARUN_1.WithSegs.mmap_fixrw_args"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_off_aligned_b"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_anon_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.w_is0"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_modeled_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_noaccess_b"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_fixed_rw_b"; "OSSVerify.KrLib.AHeap.ACeil.atop_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "Corelib.Init.Datatypes.app"; "ARUN_1.WithSegs.fixrw_outcome"; "ARUN_1.WithSegs.mmap_norep_args"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_noreplace_noaccess_b"; "ARUN_1.WithSegs.norep_outcome"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.WithSegs.anon_flags_ok"; "ARUN_1.WithSegs.mmap_anon_args"; "ARUN_1.WithSegs.anon_outcome"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.MState.MSsvc"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.ITree.resp"; "LinuxProcessSemantics.LinuxProcessSem.State.map_remove"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Mmap.check_munmap"; "ARUN_1.WithSegs.munmap_args"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "ARUN_1.WithSegs.munmap_model"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm.Madvise.check_madvise"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.int32"; "ARUN_1.WithSegs.madvise_args"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "ARUN_1.WithSegs.madvise_model"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma materialize_nil : forall mo, materialize_model_accesses mo [] = Some mo.
Proof.
  intros mo. apply newly_nil_materialize. unfold newly_materialized_pages. cbn. reflexivity.
Qed.

#[using="Type"] Lemma page_round_up_mod4096 : forall x, page_round_up_Z x mod 4096 = 0.
Proof. intros x. unfold page_round_up_Z, page_size. apply Z_mod_mult. Qed.

(* Was an encoded statement (CDefT.buildp); written out from its decode (cdeft_print.py), not
   re-encoded, with one premise added: [RomBase.sys_rob segs (mkCfg ms mo)], which [aevt_step]
   now asks for (the run_segments lift; see Lib/AEvt.v).  Both callers below name a system call
   whose specification does not read memory (222 mmap, 233 madvise) and discharge it by
   [RomBase.sys_rob_memfree]. *)
#[using="Type"] Lemma aevt_sys : forall (Q : config -> Prop) (ms : machine_state) (mo : Model) (x8 : bv 64),
  ms_svc_pending ms = Some x8 ->
  m_halted mo = None ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
     evs = [] /\ m_halted mo' = None /\ syscall_effect_accesses eff = []
     /\ Q (mkCfg (ITree.nret ms eff) mo')) ->
  ~ syscall_spec (sys_input segs ms x8) mo Unmodeled ->
  RomBase.sys_rob segs (mkCfg ms mo) ->
  AEvt.aevt segs Q (mkCfg ms mo).
Proof.
  intros Q ms mo x8 Hsvc Hh HQ HU Hrob.
  assert (PROG : exists eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs)).
  { pose proof (receptive (sys_input segs ms x8) mo) as Hr.
    destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
    - dexists eff, mo', evs. exact Hr.
    - exfalso. exact (HU Hr). }
  apply aevt_step.
  - ddestruct PROG as (eff & mo' & evs & Hs). destruct (HQ _ _ _ Hs) as (-> & Hh' & Hacc & _).
    exists (mkCfg (nret ms eff) mo'). unfold nret. eapply sstep_syscall; eauto.
    rewrite Hacc. apply materialize_nil.
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
    + destruct (HQ _ _ _ Hsp) as (_ & _ & Hacc & HQ'). rewrite Hacc, materialize_nil in Hm.
      inversion Hm; subst. inversion E; subst. apply aevt_now. exact HQ'.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). congruence.
    + exfalso. destruct (HQ _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
  - exact Hrob.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fix_flags_ok (flags : Z) : Prop := flags = 0x32 \/ flags = 0x4032.

Definition mmap_fixrw_args (ms : machine_state) (addr nZ flags : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "(10.(4.(3.&40.)(1:.O4.(1;.&5.+:.$1<.))(1=.&40.O3.))(10.(4.$1>.(1?.(20.&40.(1:.O4.(1;.&5.+;.$1<.))))O2.)(10.(17.(4.(3.&40.)(1:.O4.(1;.&5.+;.$1<.))(1=.&40.=)))(10.(4.(3.&40.)(1:.O4.(1;.&5.+<.$1<.))(1=.&40.+3.))(10.(4.(3.&40.)(1:.O4.(1;.&5.+=.$1<.))(1=.&40.O1.))(10.(4.(3.&40.)(1:.O4.(1;.&5.+>.$1<.))(1=.&40.-1.))(10.(4.(3.&40.)(1:.O4.(1;.&5.+?.$1<.))(1=.&40.=))(10.(4.$1>.(21.O3.+1000.)=)(10.(22.=O3.)(10.(22.=O2.)(10.(23.(24.O3.O2.)(25.VhAR,))(26.O1.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fixrw_commit (flags addr nZ : Z) (mo : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Zh,$27.(28.O1.)Za,(3.&40.)(1=.&40.O3.)Zn,(3.&40.)(1=.&40.O2.)(29.(1=.&40.O4.)R2.R1.(2:.(2;.R3.R2.R1.)O1.))")
(* [comment removed for export] *).
Definition fixrw_destroyed (addr nZ : Z) (mo : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Zh,$27.(28.O1.)Za,(3.&40.)(1=.&40.O3.)Zn,(3.&40.)(1=.&40.O2.)(2<.R2.R1.(2=.R3.R2.R1.)O1.)")
(* [comment removed for export] *).
Definition fixrw_fresh (flags addr nZ : Z) (mo : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Zh,$27.(28.O1.)Za,(3.&40.)(1=.&40.O3.)Zn,(3.&40.)(1=.&40.O2.)(2>.(1=.&40.O4.)R2.R1.(2:.(2?.(30.R3.)(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)R2.R1.)(33.R3.))(34.R3.)(35.R3.)(36.R3.)(37.R3.)(38.R3.)(39.R3.))O1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma halted_with_mmap_backing : forall f a n mo, m_halted (with_mmap_backing f a n mo) = m_halted mo.
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b f); destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.
#[using="Type"] Lemma halted_fixrw_commit : forall f addr nZ mo, m_halted (fixrw_commit f addr nZ mo) = m_halted mo.
Proof. intros. unfold fixrw_commit, with_mmap_replacement. rewrite halted_with_mmap_backing. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.
#[using="Type"] Lemma halted_fixrw_destroyed : forall addr nZ mo, m_halted (fixrw_destroyed addr nZ mo) = m_halted mo.
Proof. intros. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.
#[using="Type"] Lemma halted_fixrw_fresh : forall f addr nZ mo, m_halted (fixrw_fresh f addr nZ mo) = m_halted mo.
Proof. intros. unfold fixrw_fresh. rewrite halted_with_mmap_backing. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma vmmaps_with_mmap_backing : forall f a n mo, m_vmmaps (with_mmap_backing f a n mo) = m_vmmaps mo.
Proof. intros. unfold with_mmap_backing, vm_add_lazy. destruct (mmap_noreserve_b f); destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

(* [comment removed for export] *)
Inductive fixrw_outcome (flags addr nZ : Z) (mo : Model) : resp -> Model -> Prop :=
| FO_enomem_kept : forall e, In e mmap_errnos -> fixrw_outcome flags addr nZ mo (mkEffectU (errno_ret e) [] [] [] [] []) mo
| FO_enomem_destroyed : forall e, In e mmap_errnos ->
    map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
    fixrw_outcome flags addr nZ mo (mkEffectU (errno_ret e) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []) (fixrw_destroyed addr nZ mo)
| FO_commit : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
    fixrw_outcome flags addr nZ mo (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) (fixrw_commit flags addr nZ mo)
| FO_fresh : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
    fixrw_outcome flags addr nZ mo (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) (fixrw_fresh flags addr nZ mo).

#[using="Type"] Lemma mmap_check : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmodel,$2.Peff,$:.P,(4.$1>.(20.&40.R3.)+=>.)(4.$3:.(3;.(>.Vsegs,R5.R4.)R2.R3.)(3<.(1:.R5.(1;.&5.+:.$1<.))(1:.R5.(1;.&5.+;.$1<.))(1:.R5.(1;.&5.+<.$1<.))(1:.R5.(1;.&5.+=.$1<.))(1:.R5.(1;.&5.+>.$1<.))(1:.R5.(1;.&5.+?.$1<.))R2.R3.))")
(* [comment removed for export] *).
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fixrw_gates : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Paddr,$1>.PnZ,$1>.Pflags,$1>.P,(3=.R4.R3.R2.R1.)(10.(4.$3>.(3?.(1:.R5.(1;.&5.+?.$1<.)))$40.)(10.(4.$3>.(41.(1:.R5.(1;.&5.+=.$1<.)))$40.)(10.(4.$3>.(42.(1:.R5.(1;.&5.+;.$1<.)))$43.)(10.(4.$3>.(44.(1:.R5.(1;.&5.+<.$1<.))(1:.R5.(1;.&5.+=.$1<.))(1:.R5.(1;.&5.+?.$1<.)))$43.)(10.(4.$3>.(45.(1:.R5.(1;.&5.+<.$1<.))(1:.R5.(1;.&5.+=.$1<.))(1:.R5.(1;.&5.+?.$1<.)))$43.)(10.(4.$3>.(46.(1:.R5.(1;.&5.+<.$1<.))(1:.R5.(1;.&5.+=.$1<.))(1:.R5.(1;.&5.+?.$1<.)))$43.)(4.$3>.(47.(1:.R5.(1;.&5.+<.$1<.))(1:.R5.(1;.&5.+=.$1<.))(1:.R5.(1;.&5.+?.$1<.)))$40.)))))))")
(* [comment removed for export] *).
Proof.
  (intros ms addr nZ flags dd_H; ddestruct dd_H as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & _ & _ & _ & _ & FL)).
  rewrite H12, H13, H15. split; [vm_compute; reflexivity|]. split; [destruct FL as [-> | ->]; vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H11|].
  destruct FL as [-> | ->]; repeat split; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac fixrw_prep Hs mo addr nZ ATOP G H10 Hn AL :=
  let Ga := fresh "Ga" in let Gb := fresh "Gb" in let G0 := fresh "G0" in let G1 := fresh "G1" in
  let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  let L := fresh "L" in let L2 := fresh "L2" in let L3 := fresh "L3" in
  destruct G as (Ga & Gb & G0 & G1 & G2 & G3 & G4);
  unfold check_mmap, check_mmap_fixed_overflow in Hs; rewrite Ga, Gb, G0, G1, G2, G3, G4 in Hs; cbn [negb] in Hs; cbv zeta in Hs;
  rewrite H10 in Hs; rewrite !unsigned_lit in Hs by lia; rewrite Hn in Hs;
  destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|];
  destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]; cbn [negb] in Hs;
  change page_size with 4096 in Hs; rewrite (proj2 (Z.eqb_eq _ _) AL) in Hs; cbn [negb] in Hs;
  destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]; cbn [negb] in Hs.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixrw_inv : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.Pflags,$1>.Peff,$:.Pmo',$2.Pevs,(;.$<.)P,(4.$1>.(20.&40.R8.)+=>.)P,(3=.R:.R7.R6.R5.)P,(48.VhAR,(49.(28.R9.)))P,(4.$3>.(4:.(30.(28.R:.))(1=.&40.R9.)(1=.&40.R8.))$40.)P,(4;.(4.$3>.(4<.(33.(28.R;.))(1=.&40.R:.)(1=.&40.R9.))$40.)(4.$3>.(4:.(4=.(12.(3.&40.)(3.&40.))(30.(28.R;.))(33.(28.R;.)))(1=.&40.R:.)(1=.&40.R9.))$40.))P,(=.(>.Vsegs,R>.R=.)R<.(?.$:.R8.R7.R6.))(10.(4.(;.$<.)R7.(11.$<.))(4>.R:.R<.R;.R=.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ flags eff mo' evs Hno HA ATOP RF CASES Hs. aceilb.
  pose proof (fixrw_gates ms addr nZ flags HA) as G.
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE & FL).
  apply check_syscall_ok_iff in Hs. rewrite (mmap_check ms x8 mo eff Hno) in Hs.
  fixrw_prep Hs mo addr nZ ATOP G H10 Hn AL.
  rewrite RF in Hs. cbn [andb] in Hs.
  destruct (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:MC.
  - (* [comment removed for export] *)
    destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
    destruct ws as [|? ?]; [|discriminate]. destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:ER.
    + apply errno_ret_in_true in ER. ddestruct ER as (e & HIn & ->).
      destruct zs as [|? ?]; [|discriminate].
      destruct us as [|u us'].
      * inversion Hs; subst. split; [reflexivity|]. apply FO_enomem_kept. exact HIn.
      * (* [comment removed for export] *)
        destruct (listNN_eqb (u :: us') [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LU; [|discriminate].
        apply listNN_eqb_eq in LU. rewrite LU. inversion Hs; subst. split; [reflexivity|].
        apply FO_enomem_destroyed; [exact HIn| exact MC].
    + destruct us as [|? ?]; [|discriminate].
      destruct (bv_eqb r (Z_to_bv 64 addr)) eqn:RR; cbn [andb] in Hs; [|discriminate].
      destruct (listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LZ; cbn [andb] in Hs; [|discriminate].
      destruct (mmap_fixed_rw_budget_ok (areg ms 13) mo (Z_to_bv 64 addr) (Z_to_bv 64 nZ)); [|discriminate].
      apply bv_eqb_eq in RR. apply listNN_eqb_eq in LZ. subst r zs.
      inversion Hs; subst. split; [reflexivity|]. rewrite H13. apply FO_commit. exact MC.
  - (* [comment removed for export] *)
    destruct CASES as [MC'|FR]; [congruence|]. rewrite FR in Hs.
    destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
    destruct ws as [|? ?]; [|discriminate]. destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:ER.
    + apply errno_ret_in_true in ER. ddestruct ER as (e & HIn & ->).
      destruct zs as [|? ?]; [|discriminate]. inversion Hs; subst. split; [reflexivity|]. apply FO_enomem_kept. exact HIn.
    + destruct (bv_eqb r (Z_to_bv 64 addr)) eqn:RR; cbn [andb] in Hs; [|discriminate].
      destruct (listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LZ; cbn [andb] in Hs; [|discriminate].
      destruct (mmap_noreserve_backed_ok (areg ms 13) mo nZ); [|discriminate].
      apply bv_eqb_eq in RR. apply listNN_eqb_eq in LZ. subst r zs.
      inversion Hs; subst. split; [reflexivity|]. rewrite H13. apply FO_fresh. exact FR.
Qed.

#[using="Type"] Lemma mmap_fixrw_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.Pflags,$1>.P,(4.$1>.(20.&40.R5.)+=>.)P,(3=.R7.R4.R3.R2.)P,(48.VhAR,(49.(28.R6.)))P,(4.$3>.(4:.(30.(28.R7.))(1=.&40.R6.)(1=.&40.R5.))$40.)P,(4;.(4.$3>.(4<.(33.(28.R8.))(1=.&40.R7.)(1=.&40.R6.))$40.)(4.$3>.(4:.(4=.(12.(3.&40.)(3.&40.))(30.(28.R8.))(33.(28.R8.)))(1=.&40.R7.)(1=.&40.R6.))$40.))(17.(=.(>.Vsegs,R;.R:.)R9.(18.$:.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ flags Hno HA ATOP RF CASES Hs. aceilb.
  pose proof (fixrw_gates ms addr nZ flags HA) as G.
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE & FL).
  apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
  rewrite (mmap_check ms x8 mo _ Hno) in Hs.
  fixrw_prep Hs mo addr nZ ATOP G H10 Hn AL.
  rewrite RF in Hs. cbn [andb] in Hs.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  destruct (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:MC.
  - cbv beta iota zeta in Hs. rewrite E in Hs.
    match type of Hs with (if ?b then _ else _) = _ => destruct b end; discriminate.
  - destruct CASES as [MC'|FR]; [congruence|]. rewrite FR in Hs. cbv beta iota zeta in Hs. rewrite E in Hs.
    match type of Hs with (if ?b then _ else _) = _ => destruct b end; discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mmap_norep_args (ms : machine_state) (addr nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "(10.(4.(3.&40.)(1:.O3.(1;.&5.+:.$1<.))(1=.&40.O2.))(10.(4.$1>.(1?.(20.&40.(1:.O3.(1;.&5.+;.$1<.))))O1.)(10.(17.(4.(3.&40.)(1:.O3.(1;.&5.+;.$1<.))(1=.&40.=)))(10.(4.(3.&40.)(1:.O3.(1;.&5.+<.$1<.))(1=.&40.=))(10.(4.(3.&40.)(1:.O3.(1;.&5.+=.$1<.))(1=.&40.+104022.))(10.(4.(3.&40.)(1:.O3.(1;.&5.+>.$1<.))(1=.&40.-1.))(10.(4.(3.&40.)(1:.O3.(1;.&5.+?.$1<.))(1=.&40.=))(10.(4.$1>.(21.O2.+1000.)=)(10.(22.=O2.)(10.(22.=O1.)(23.(24.O2.O1.)(25.VhAR,))))))))))))")
(* [comment removed for export] *).

Definition norep_grant (addr nZ : Z) (mo : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Zh,$27.(28.O1.)Za,(3.&40.)(1=.&40.O3.)Zn,(3.&40.)(1=.&40.O2.)(2>.(1=.&40.+104022.)R2.R1.(2:.(2?.(30.R3.)(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)R2.R1.)(33.R3.))(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)R2.R1.)(34.R3.))(35.R3.)(36.R3.)(37.R3.)(38.R3.)(39.R3.))O1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma halted_norep_grant : forall addr nZ mo, m_halted (norep_grant addr nZ mo) = m_halted mo.
Proof. intros. unfold norep_grant. rewrite halted_with_mmap_backing. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.
#[using="Type"] Lemma alloc_top_norep_grant : forall addr nZ mo, alloc_top (m_vmmaps (norep_grant addr nZ mo)) = alloc_top (m_vmmaps mo).
Proof. intros. unfold norep_grant. rewrite vmmaps_with_mmap_backing. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

(* [comment removed for export] *)
Inductive norep_outcome (addr nZ : Z) (mo : Model) : resp -> Model -> Prop :=
| NO_enomem : norep_outcome addr nZ mo (mkEffectU (errno_ret ENOMEM) [] [] [] [] []) mo
| NO_eexist : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = false ->
    norep_outcome addr nZ mo (mkEffectU (errno_ret EEXIST) [] [] [] [] []) mo
| NO_grant : region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
    norep_outcome addr nZ mo (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []) (norep_grant addr nZ mo).

#[using="Type"] Lemma norep_gates : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Paddr,$1>.PnZ,$1>.P,(4?.R3.R2.R1.)(10.(4.$3>.(3?.(1:.R4.(1;.&5.+?.$1<.)))$40.)(10.(4.$3>.(41.(1:.R4.(1;.&5.+=.$1<.)))$40.)(10.(4.$3>.(42.(1:.R4.(1;.&5.+;.$1<.)))$43.)(10.(4.$3>.(44.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$43.)(10.(4.$3>.(45.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$43.)(10.(4.$3>.(46.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$43.)(10.(4.$3>.(47.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$43.)(4.$3>.(50.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$40.))))))))")
(* [comment removed for export] *).
Proof.
  (intros ms addr nZ dd_H; ddestruct dd_H as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & _)).
  rewrite H12, H13, H15. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H11|].
  repeat split; vm_compute; reflexivity.
Qed.

Local Ltac norep_prep Hs mo addr nZ ATOP G H10 Hn AL :=
  let Ga := fresh "Ga" in let Gb := fresh "Gb" in let G0 := fresh "G0" in let G1 := fresh "G1" in
  let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in let G5 := fresh "G5" in
  let L := fresh "L" in let L2 := fresh "L2" in let L3 := fresh "L3" in
  destruct G as (Ga & Gb & G0 & G1 & G2 & G3 & G4 & G5);
  unfold check_mmap, check_mmap_fixed_overflow in Hs; rewrite Ga, Gb, G0, G1, G2, G3, G4, G5 in Hs; cbn [negb] in Hs; cbv zeta in Hs;
  rewrite H10 in Hs; rewrite !unsigned_lit in Hs by lia; rewrite Hn in Hs;
  destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|];
  destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]; cbn [negb] in Hs;
  change page_size with 4096 in Hs; rewrite (proj2 (Z.eqb_eq _ _) AL) in Hs; cbn [negb] in Hs;
  destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]; cbn [negb] in Hs.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_norep_inv : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.Peff,$:.Pmo',$2.Pevs,(;.$<.)P,(4.$1>.(20.&40.R7.)+=>.)P,(4?.R9.R6.R5.)P,(48.VhAR,(49.(28.R8.)))P,(=.(>.Vsegs,R;.R:.)R9.(?.$:.R6.R5.R4.))(10.(4.(;.$<.)R5.(11.$<.))(51.R9.R8.R:.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ eff mo' evs Hno HA ATOP Hs. aceilb.
  pose proof (norep_gates ms addr nZ HA) as G.
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE).
  apply check_syscall_ok_iff in Hs. rewrite (mmap_check ms x8 mo eff Hno) in Hs.
  norep_prep Hs mo addr nZ ATOP G H10 Hn AL.
  destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:FR.
  - (* [comment removed for export] *)
    destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
    destruct ws as [|? ?]; [|discriminate]. destruct zs as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:ER.
    + apply errno_ret_in_true in ER. ddestruct ER as (e & HIn & ->). destruct HIn as [<-|[]].
      destruct us as [|? ?]; [|discriminate]. inversion Hs; subst. split; [reflexivity|]. apply NO_enomem.
    + destruct (bv_eqb r (Z_to_bv 64 addr)) eqn:RR; cbn [andb] in Hs; [|discriminate].
      destruct (listNN_eqb us [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LU; [|discriminate].
      apply bv_eqb_eq in RR. apply listNN_eqb_eq in LU. subst r us.
      inversion Hs; subst. split; [reflexivity|]. rewrite H13. apply NO_grant. exact FR.
  - (* [comment removed for export] *)
    destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
    destruct ws as [|? ?]; [|discriminate]. destruct zs as [|? ?]; [|discriminate]. destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
    destruct (errno_ret_in mmap_errnos r) eqn:ER; cbn [orb] in Hs.
    + apply errno_ret_in_true in ER. ddestruct ER as (e & HIn & ->). destruct HIn as [<-|[]].
      inversion Hs; subst. split; [reflexivity|]. apply NO_enomem.
    + destruct (bv_eqb r (errno_ret EEXIST)) eqn:RE; [|discriminate]. apply bv_eqb_eq in RE. subst r.
      inversion Hs; subst. split; [reflexivity|]. apply NO_eexist. exact FR.
Qed.

#[using="Type"] Lemma mmap_norep_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.P,(4.$1>.(20.&40.R4.)+=>.)P,(4?.R6.R3.R2.)P,(48.VhAR,(49.(28.R5.)))(17.(=.(>.Vsegs,R8.R7.)R6.(18.$:.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ Hno HA ATOP Hs. aceilb.
  pose proof (norep_gates ms addr nZ HA) as G.
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE).
  apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
  rewrite (mmap_check ms x8 mo _ Hno) in Hs.
  norep_prep Hs mo addr nZ ATOP G H10 Hn AL.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity.
  destruct (region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) eqn:FR;
    cbv beta iota zeta in Hs; rewrite E in Hs; cbn [orb] in Hs;
    match type of Hs with (if ?b then _ else _) = _ => destruct b end; discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma contained_not_free : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "PR,(;.(12.(3.&40.)(3.&40.)))PM,(;.(12.(3.&40.)(3.&40.)))Pa,(3.&40.)Pn,(3.&40.)P,(22.=(20.&40.R1.))P,(22.(24.(20.&40.R3.)(20.&40.R2.))(52.+2.+40.))P,(4.$3>.(4<.R5.R4.R3.)$40.)(4.$3>.(4:.(4=.(12.(3.&40.)(3.&40.))R7.R6.)R5.R4.)$43.)")
(* [comment removed for export] *).
Proof.
  intros R M a n Hn Hov MC. destruct (region_free (R ++ M) a n) eqn:RF; [| reflexivity]. exfalso.
  unfold map_contains in MC. apply existsb_exists in MC. ddestruct MC as ([b sz] & Hin & MCe). cbn [fst snd] in MCe.
  apply andb_prop in MCe. destruct MCe as [M1 M2]. apply Z.leb_le in M1. apply Z.leb_le in M2.
  pose proof (region_free_In (R ++ M) a n b sz RF ltac:(apply in_app_iff; right; exact Hin)) as OV.
  destruct OV as [OV|OV]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition anon_flags_ok (flags : Z) : Prop := flags = 0x22 \/ flags = 0x4022.

Definition mmap_anon_args (ms : machine_state) (nZ flags : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "(10.(4.(3.&40.)(1:.O3.(1;.&5.+:.$1<.))(1=.&40.=))(10.(4.$1>.(1?.(20.&40.(1:.O3.(1;.&5.+;.$1<.))))O2.)(10.(17.(4.(3.&40.)(1:.O3.(1;.&5.+;.$1<.))(1=.&40.=)))(10.(4.(3.&40.)(1:.O3.(1;.&5.+<.$1<.))(1=.&40.+3.))(10.(4.(3.&40.)(1:.O3.(1;.&5.+=.$1<.))(1=.&40.O1.))(10.(4.(3.&40.)(1:.O3.(1;.&5.+>.$1<.))(1=.&40.-1.))(10.(4.(3.&40.)(1:.O3.(1;.&5.+?.$1<.))(1=.&40.=))(10.(22.=O2.)(53.O1.)))))))))")
(* [comment removed for export] *).

Definition anon_grant (flags : Z) (a : word) (nZ : Z) (mo : Model) : Model := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Zh,$27.(28.O1.)Zn,(3.&40.)(1=.&40.O2.)(2>.(1=.&40.O4.)O3.R1.(2:.(2?.(30.R2.)(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)O3.R1.)(33.R2.))(34.R2.)(35.R2.)(36.R2.)(37.R2.)(38.R2.)(39.R2.))O1.))")
(* [comment removed for export] *).

#[using="Type"] Lemma halted_anon_grant : forall f a nZ mo, m_halted (anon_grant f a nZ mo) = m_halted mo.
Proof. intros. unfold anon_grant. rewrite halted_with_mmap_backing. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

(** THE CHECKER'S OWN PLACEMENT TEST, NAMED.

    At #38 the modeled-anon arm of [check_mmap] gates on
    [Placement.linux_place_is] ([Checks/Sys/Mm/Mmap.v:111]), and
    [AHeap.ASysS.grant_placed]'s FIRST conjunct is exactly that test.  An
    inversion of an mmap the checker already accepted therefore has the test
    in hand, so [AO_grant] can carry it; the SECOND conjunct of
    [grant_placed] ([kHighMemBeg < a]) is not something an inversion can
    invent, and is rebuilt by a caller holding the mark
    ([AMark.heap_mark_above]).

    Named here rather than written inline so that files downstream of [ASys]
    can speak of it without naming the model module path, and so that
    [grant_placed]'s own text is untouched: [placed_at nZ mo a] is
    convertible with [proj1] of [grant_placed nZ mo a]. *)
Definition placed_at (nZ : Z) (mo : Model) (a : word) : Prop :=
  LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is
    (m_vmmaps mo) (kb_thp (m_kernel mo)) (Z_to_bv 64 0) nZ a = true.

Inductive anon_outcome (flags nZ : Z) (mo : Model) : resp -> Model -> Prop :=
| AO_enomem : forall e, In e mmap_errnos -> anon_outcome flags nZ mo (mkEffectU (errno_ret e) [] [] [] [] []) mo
| AO_grant : forall a : word,
    bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a ->
    placed_at nZ mo a ->
    bv_unsigned a + nZ <= ACEIL ->
    region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true ->
    anon_outcome flags nZ mo (mkEffect a [] [(a, Z_to_bv 64 nZ)]) (anon_grant flags a nZ mo).

#[using="Type"] Lemma anon_gates : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.PnZ,$1>.Pflags,$1>.P,(54.R3.R2.R1.)(10.(4.$3>.(3?.(1:.R4.(1;.&5.+?.$1<.)))$40.)(10.(4.$3>.(41.(1:.R4.(1;.&5.+=.$1<.)))$40.)(10.(4.$3>.(42.(1:.R4.(1;.&5.+;.$1<.)))$43.)(4.$3>.(44.(1:.R4.(1;.&5.+<.$1<.))(1:.R4.(1;.&5.+=.$1<.))(1:.R4.(1;.&5.+?.$1<.)))$40.))))")
(* [comment removed for export] *).
Proof.
  (intros ms nZ flags dd_H; ddestruct dd_H as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & N0 & FL)).
  rewrite H12, H13, H15. split; [vm_compute; reflexivity|]. split; [destruct FL as [-> | ->]; vm_compute; reflexivity|].
  split; [unfold w_is0; apply bv_eqb_neq; exact H11|].
  destruct FL as [-> | ->]; vm_compute; reflexivity.
Qed.

#[using="Type"] Lemma mmap_anon_inv : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.PnZ,$1>.Pflags,$1>.Peff,$:.Pmo',$2.Pevs,(;.$<.)P,(4.$1>.(20.&40.R7.)+=>.)P,(54.R9.R6.R5.)P,(48.VhAR,(49.(28.R8.)))P,(=.(>.Vsegs,R;.R:.)R9.(?.$:.R6.R5.R4.))(10.(4.(;.$<.)R5.(11.$<.))(55.R8.R9.R:.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo nZ flags eff mo' evs Hno HA ATOP Hs.
  dpose (anon_gates ms nZ flags HA) as (Ga & Gb & G0 & G1).
  ddestruct HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & N0 & FL).
  apply check_syscall_ok_iff in Hs. rewrite (mmap_check ms x8 mo eff Hno) in Hs.
  unfold check_mmap, check_mmap_fixed_overflow in Hs. rewrite Ga, Gb, G0, G1 in Hs. cbn [negb] in Hs. cbv iota in Hs. cbv zeta in Hs.
  (* LPS 727298f3: the call's hint is NULL ([H10]), which no decline holds of *)
  lazymatch type of Hs with context [place_declined_b ?dk ?dh ?da ?dn] =>
    replace (place_declined_b dk dh da dn) with false in Hs
      by (rewrite (H10 : da = Z_to_bv 64 0); reflexivity) end.
  rewrite Hn, H13 in Hs.
  destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
  destruct ws as [|? ?]; [|discriminate]. destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:ER.
  - apply errno_ret_in_true in ER. ddestruct ER as (e & HIn & ->).
    destruct zs as [|? ?]; [|discriminate]. inversion Hs; subst. split; [reflexivity|]. apply AO_enomem. exact HIn.
  - (* at 08b1429 the grant is the address Linux places ([Placement.linux_place_is]);
       its four admissibility facts follow ([linux_place_is_admissible]) *)
    lazymatch type of Hs with context [LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is ?h ?t ?a nZ r] =>
      destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is h t a nZ r) eqn:LP;
      cbn [andb] in Hs; [|discriminate];
      assert (Hnal : (nZ mod page_size = 0)%Z) by (change page_size with 4096; rewrite <- Hn; apply page_round_up_mod4096);
      assert (Hn0 : (0 < nZ)%Z) by lia;
      destruct (LinuxProcessSemantics.LinuxProcessSem.Checks.Placement.linux_place_is_admissible h t a nZ r Hn0 Hnal LP)
        as (AL & R0 & CE0 & FR)
    end.
    change page_size with 4096 in AL.
    (* #38: the gate the checker passed IS [placed_at] -- the call's NULL a0
       ([H10]) lines its hint up with [placed_at]'s [Z_to_bv 64 0].  This is
       the half of [ASysS.grant_placed] an inversion can supply. *)
    assert (PL : placed_at nZ mo r)
      by (unfold placed_at;
          first [exact LP | rewrite <- H10; exact LP | rewrite H10 in LP; exact LP]).
    assert (CE : bv_unsigned r + nZ <= ACEIL).
    { apply (atop_grant _ _ _ ATOP AL); [| exact CE0]. rewrite <- Hn. apply page_round_up_mod4096. }
    destruct (mmap_noreserve_backed_ok (Z_to_bv 64 flags) mo nZ); cbn [andb] in Hs; [|discriminate].
    destruct (listNN_eqb zs [(r, Z_to_bv 64 nZ)]) eqn:LZ; [|discriminate].
    apply listNN_eqb_eq in LZ. subst zs. inversion Hs; subst. split; [reflexivity|].
    apply AO_grant; assumption.
Qed.

#[using="Type"] Lemma mmap_anon_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.PnZ,$1>.Pflags,$1>.P,(4.$1>.(20.&40.R4.)+=>.)P,(54.R6.R3.R2.)(17.(=.(>.Vsegs,R7.R6.)R5.(18.$:.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo nZ flags Hno HA Hs.
  dpose (anon_gates ms nZ flags HA) as (Ga & Gb & G0 & G1).
  apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
  rewrite (mmap_check ms x8 mo _ Hno) in Hs. unfold check_mmap, check_mmap_fixed_overflow in Hs. rewrite Ga, Gb, G0, G1 in Hs.
  cbn [negb] in Hs. cbv beta iota zeta in Hs.
  (* LPS 727298f3: the call's hint is NULL, which no decline holds of *)
  pose proof HA as HA0. destruct HA0 as [H10 _].
  lazymatch type of Hs with context [place_declined_b ?dk ?dh ?da ?dn] =>
    replace (place_declined_b dk dh da dn) with false in Hs
      by (rewrite (H10 : da = Z_to_bv 64 0); reflexivity) end.
  cbv iota in Hs.
  assert (E : errno_ret_in mmap_errnos (Z_to_bv 64 0) = false) by reflexivity. rewrite E in Hs.
  match type of Hs with (if ?b then _ else _) = _ => destruct b end; discriminate.
Qed.

#[using="Type"] Lemma aevt_mmap_anon : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "PQ,P,$0.SpPR,(56.&5.(3.&40.))PF,(56.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.PnZ,$1>.Pflags,$1>.Zms,$1.(57.R9.R8.R7.(1=.&40.+=>.)R6.R5.R4.(58.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(48.VhAR,(49.(28.R5.)))P,(54.R3.R5.R4.)P,Peff,$59.Pmo',$2.P,(55.R7.R8.R9.R2.R1.)A1.R11.(15.(16.R7.R3.)R2.)(19.Vsegs,R?.(15.R5.R8.))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo nZ flags ms Hh ATOP HA HQ.
  eapply aevt_sys with (x8 := Z_to_bv 64 222); [reflexivity| exact Hh| | |].
  - intros eff mo' evs Hs.
    assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
    destruct (mmap_anon_inv ms (Z_to_bv 64 222) mo nZ flags eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    split; [reflexivity|]. split; [|split; [| apply HQ; exact OUT]].
    + destruct OUT; rewrite ?halted_anon_grant; exact Hh.
    + destruct OUT; reflexivity.
  - eapply (mmap_anon_no_unmodeled ms (Z_to_bv 64 222)); eauto; vm_compute; reflexivity.
  - eapply (RomBase.sys_rob_memfree segs); [reflexivity |]. exact RomBase.memfree_222.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_args (ms : machine_state) (addr nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "(10.(4.(3.&40.)(1:.O3.(1;.&5.+:.$1<.))(1=.&40.O2.))(10.(4.$1>.(1?.(20.&40.(1:.O3.(1;.&5.+;.$1<.))))O1.)(10.(17.(4.(3.&40.)(1:.O3.(1;.&5.+;.$1<.))(1=.&40.=)))(10.(4.$1>.(21.O2.+1000.)=)(10.(23.=O2.)(10.(22.=O1.)(23.(24.O2.O1.)(25.VhAR,))))))))")
(* [comment removed for export] *).

(* 08b1429: a successful munmap cuts [addr, addr + n) out of both ledgers
   ([Mmap.mmap_fixed_destroyed_next], used by [Checks.Sys.Mm.Mmap.check_munmap]); the
   model's own Common/MmapSim.munmap_model made the same change.  Plain text: the
   serialised term named the pre-revision [map_remove] form. *)
Definition munmap_model (addr nZ : Z) (mo : Model) : Model :=
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in
  let n := Z_to_bv 64 nZ in
  with_mmap_destroyed a n (mmap_fixed_destroyed_next h a n) mo.

#[using="Type"] Lemma halted_munmap_model : forall addr nZ mo, m_halted (munmap_model addr nZ mo) = m_halted mo.
Proof. intros. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

#[using="Type"] Lemma munmap_check : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmodel,$2.Peff,$:.P,(4.$1>.(20.&40.R3.)+=7.)(4.$3:.(3;.(>.Vsegs,R5.R4.)R2.R3.)(5<.(1:.R5.(1;.&5.+:.$1<.))(1:.R5.(1;.&5.+;.$1<.))R2.R3.))")
(* [comment removed for export] *).
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Local Ltac munmap_prep Hs ms addr nZ H10 H11 Hn AL MH :=
  let L := fresh "L" in
  unfold check_munmap in Hs; rewrite H10 in Hs;
  rewrite !unsigned_lit in Hs by lia; change page_size with 4096 in Hs;
  rewrite (proj2 (Z.eqb_eq _ _) AL) in Hs;
  replace (w_is0 (areg ms 11)) with false in Hs by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H11); cbn [negb orb] in Hs;
  rewrite Hn in Hs;
  destruct (Z.ltb_spec0 TASK_SIZE (addr + nZ)) as [L|L]; [unfold TASK_SIZE in L; lia|];
  rewrite MH in Hs.

(* 08b1429: munmap of an exact mapping may also answer an injected munmap_errnos
   refusal ([Mmap.munmap_spec]'s [errno_from munmap_errnos] arm), which changes
   nothing; the old statement (success only) is false at the revision.  Plain text. *)
#[using="Type"] Lemma munmap_inv : forall ms x8 mo addr nZ eff mo' evs,
  bv_unsigned x8 = 215 ->
  munmap_args ms addr nZ ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
  evs = [] /\
  ((errno_ret_in munmap_errnos (eff_ret eff) = true
    /\ eff = mkEffectU (eff_ret eff) [] [] [] [] [] /\ mo' = mo)
   \/ (eff = mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []
       /\ mo' = munmap_model addr nZ mo)).
Proof.
  (intros ms x8 mo addr nZ eff mo' evs Hno dd_H; ddestruct dd_H as (H10 & Hn & H11 & AL & A0 & N0 & CE); intros MH Hs). aceilb.
  apply check_syscall_ok_iff in Hs. rewrite (munmap_check ms x8 mo eff Hno) in Hs.
  munmap_prep Hs ms addr nZ H10 H11 Hn AL MH.
  destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
  destruct ws as [|? ?]; [|discriminate]. destruct zs as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
  destruct (errno_ret_in munmap_errnos r) eqn:ER.
  - destruct us as [|? ?]; [|discriminate]. inversion Hs; subst.
    split; [reflexivity|]. left. split; [exact ER|]. split; reflexivity.
  - destruct (w_is0 r) eqn:R0; cbn [andb] in Hs; [|discriminate].
    destruct (listNN_eqb us [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LU; [|discriminate].
    apply listNN_eqb_eq in LU. subst us. unfold w_is0 in R0. apply bv_eqb_eq in R0. subst r.
    inversion Hs; subst. split; [reflexivity|]. right. split; [reflexivity|].
    unfold munmap_model. reflexivity.
Qed.

(* The success outcome is always admitted (no refusal is forced): the witness the
   refused branch's spuriousness needs ([ASysS.munmap_refusal_spurious]). *)
#[using="Type"] Lemma munmap_grant_spec : forall ms x8 mo addr nZ,
  bv_unsigned x8 = 215 ->
  munmap_args ms addr nZ ->
  map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  syscall_spec (sys_input segs ms x8) mo
    (Ok (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [])
        (munmap_model addr nZ mo) []).
Proof.
  (intros ms x8 mo addr nZ Hno dd_H; ddestruct dd_H as (H10 & Hn & H11 & AL & A0 & N0 & CE); intros MH). aceilb.
  apply check_syscall_ok_iff. rewrite (munmap_check ms x8 mo _ Hno).
  unfold check_munmap. rewrite H10.
  rewrite !unsigned_lit by lia. change page_size with 4096.
  rewrite (proj2 (Z.eqb_eq _ _) AL).
  replace (w_is0 (areg ms 11)) with false by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H11). cbn [negb orb].
  rewrite Hn.
  destruct (Z.ltb_spec0 TASK_SIZE (addr + nZ)) as [L|L]; [unfold TASK_SIZE in L; lia|].
  rewrite MH. cbv beta iota zeta.
  replace (errno_ret_in munmap_errnos (Z_to_bv 64 0)) with false by (vm_compute; reflexivity).
  replace (w_is0 (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). cbn [andb].
  unfold munmap_model. reflexivity.
Qed.

#[using="Type"] Lemma munmap_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.P,(4.$1>.(20.&40.R4.)+=7.)P,(5=.R6.R3.R2.)P,(4.$3>.(5>.(33.(28.R5.))(1=.&40.R4.)(1=.&40.R3.))$40.)(17.(=.(>.Vsegs,R8.R7.)R6.(18.$:.)))")
(* [comment removed for export] *).
Proof.
  (intros ms x8 mo addr nZ Hno dd_H; ddestruct dd_H as (H10 & Hn & H11 & AL & A0 & N0 & CE); intros MH Hs). aceilb.
  apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
  rewrite (munmap_check ms x8 mo _ Hno) in Hs.
  munmap_prep Hs ms addr nZ H10 H11 Hn AL MH.
  cbv beta iota zeta in Hs.
  repeat match type of Hs with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition madvise_args (ms : machine_state) (addr nZ : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASys ()) "(10.(4.(3.&40.)(1:.O3.(1;.&5.+:.$1<.))(1=.&40.O2.))(10.(4.$1>.(1?.(20.&40.(1:.O3.(1;.&5.+;.$1<.))))O1.)(10.(17.(4.(3.&40.)(1:.O3.(1;.&5.+;.$1<.))(1=.&40.=)))(10.(4.(3.&40.)(1:.O3.(1;.&5.+<.$1<.))(1=.&40.+4.))(10.(4.$1>.(21.O2.+1000.)=)(10.(23.=O2.)(10.(22.=O1.)(23.(24.O2.O1.)(52.+2.+2?.)))))))))")
(* [comment removed for export] *).

Definition madvise_model (addr nZ : Z) (mo : Model) : Model :=
  madvise_dontneed_next mo (Z_to_bv 64 addr) (Z_to_bv 64 nZ).

#[using="Type"] Lemma halted_madvise_model : forall addr nZ mo, m_halted (madvise_model addr nZ mo) = m_halted mo.
Proof. intros. destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity. Qed.

#[using="Type"] Lemma madvise_check : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmodel,$2.Peff,$:.P,(4.$1>.(20.&40.R3.)+>9.)(4.$3:.(3;.(>.Vsegs,R5.R4.)R2.R3.)(62.(1:.R5.(1;.&5.+:.$1<.))(1:.R5.(1;.&5.+;.$1<.))(63.(1:.R5.(1;.&5.+<.$1<.)))R2.R3.))")
(* [comment removed for export] *).
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Local Ltac madvise_prep Hs ms addr nZ H10 H11 H12 Hn AL OKG :=
  unfold check_madvise in Hs; rewrite H10, H12 in Hs;
  rewrite !unsigned_lit in Hs by lia; change page_size with 4096 in Hs;
  rewrite (proj2 (Z.eqb_eq _ _) AL) in Hs;
  replace (madvise_dontneed_b (int32 (Z_to_bv 64 4))) with true in Hs by (vm_compute; reflexivity);
  replace (w_is0 (areg ms 11)) with false in Hs by (symmetry; unfold w_is0; apply bv_eqb_neq; exact H11); cbn [negb] in Hs;
  rewrite Hn in Hs;
  replace (two_pow_64 <=? addr + nZ) with false in Hs by (symmetry; apply Z.leb_gt; unfold two_pow_64; lia);
  cbv zeta in Hs; rewrite OKG in Hs.

#[using="Type"] Lemma madvise_inv : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.Peff,$:.Pmo',$2.Pevs,(;.$<.)P,(4.$1>.(20.&40.R7.)+>9.)P,(64.R9.R6.R5.)P,(4.$3>.(65.(28.R8.)(1=.&40.R7.)(1=.&40.R6.))$40.)P,(=.(>.Vsegs,R;.R:.)R9.(?.$:.R6.R5.R4.))(10.(4.(;.$<.)R5.(11.$<.))(10.(4.$:.R7.(5?.(1=.&40.=)(11.(12.(3.&40.)(;.(3.&8.))))(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)(1=.&40.R9.)(1=.&40.R8.))(11.(12.(3.&40.)(3.&40.))))(11.(12.(3.&40.)(3.&40.)))(11.$60.)(11.(12.(3.&40.)$13.))))(4.$2.R6.(66.R9.R8.R:.))))")
(* [comment removed for export] *).
Proof.
  (intros ms x8 mo addr nZ eff mo' evs Hno dd_H; ddestruct dd_H as (H10 & Hn & H11 & H12 & AL & A0 & N0 & CE); intros OKG Hs).
  apply check_syscall_ok_iff in Hs. rewrite (madvise_check ms x8 mo eff Hno) in Hs.
  madvise_prep Hs ms addr nZ H10 H11 H12 Hn AL OKG.
  destruct eff as [r ws zs us cs ci]. cbv beta iota zeta in Hs.
  destruct ws as [|? ?]; [|discriminate]. destruct us as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate]. destruct ci as [|? ?]; [|discriminate].
  destruct (w_is0 r) eqn:R0; cbn [andb] in Hs; [|discriminate].
  destruct (listNN_eqb zs [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) eqn:LU; [|discriminate].
  apply listNN_eqb_eq in LU. subst zs. unfold w_is0 in R0. apply bv_eqb_eq in R0. subst r.
  inversion Hs; subst. split; [reflexivity|]. split; [reflexivity|]. reflexivity.
Qed.

#[using="Type"] Lemma madvise_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "Pms,$1.Px8,(3.&40.)Pmo,$2.Paddr,$1>.PnZ,$1>.P,(4.$1>.(20.&40.R4.)+>9.)P,(64.R6.R3.R2.)P,(4.$3>.(65.(28.R5.)(1=.&40.R4.)(1=.&40.R3.))$40.)(17.(=.(>.Vsegs,R8.R7.)R6.(18.$:.)))")
(* [comment removed for export] *).
Proof.
  (intros ms x8 mo addr nZ Hno dd_H; ddestruct dd_H as (H10 & Hn & H11 & H12 & AL & A0 & N0 & CE); intros OKG Hs).
  apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
  rewrite (madvise_check ms x8 mo _ Hno) in Hs.
  madvise_prep Hs ms addr nZ H10 H11 H12 Hn AL OKG.
  cbv beta iota zeta in Hs. discriminate.
Qed.

#[using="Type"] Lemma aevt_madvise : ltac2:(CDefT.buildp (gd_tbl_ASys ()) "PQ,P,$0.SpPR,(56.&5.(3.&40.))PF,(56.&5.(3.&40.))Ppc,(3.&40.)Pfc,(3.&20.)Prv,(5.(3.&40.))Pm,P,(3.&40.)(5.(3.&8.))Pmo,$2.Paddr,$1>.PnZ,$1>.Zms,$1.(57.R9.R8.R7.(1=.&40.+>9.)R6.R5.R4.(58.Vsegs,))P,(4.(5.(3.&40.))(8.R4.)(9.(3.&40.)))P,(64.R2.R4.R3.)P,(4.$3>.(65.(28.R6.)(1=.&40.R5.)(1=.&40.R4.))$40.)P,A1.R>.(15.(16.R4.(5?.(1=.&40.=)(11.(12.(3.&40.)(;.(3.&8.))))(31.(12.(3.&40.)(3.&40.))(32.(3.&40.)(3.&40.)(1=.&40.R6.)(1=.&40.R5.))(11.(12.(3.&40.)(3.&40.))))(11.(12.(3.&40.)(3.&40.)))(11.$60.)(11.(12.(3.&40.)$13.))))(66.R6.R5.R7.))(19.Vsegs,R?.(15.R5.R8.))")
(* [comment removed for export] *).
Proof.
  intros Q R F pc fc rv m mo addr nZ ms Hh HA OKG HQ.
  eapply aevt_sys with (x8 := Z_to_bv 64 233); [reflexivity| exact Hh| | |].
  - intros eff mo' evs Hs.
    assert (E233 : bv_unsigned (Z_to_bv 64 233) = 233) by (vm_compute; reflexivity).
    ddestruct (madvise_inv ms (Z_to_bv 64 233) mo addr nZ eff mo' evs E233 HA OKG Hs) as (-> & -> & ->).
    split; [reflexivity|]. split; [|split; [reflexivity| exact HQ]].
    rewrite halted_madvise_model. exact Hh.
  - eapply (madvise_no_unmodeled ms (Z_to_bv 64 233)); eauto; vm_compute; reflexivity.
  - eapply (RomBase.sys_rob_memfree segs); [reflexivity |]. exact RomBase.memfree_233.
Qed.

End WithSegs.
End ARUN_1.
