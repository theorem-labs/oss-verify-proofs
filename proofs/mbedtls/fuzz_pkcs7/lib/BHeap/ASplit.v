(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude DispatchCompute.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac ITree Nodes SysStep AEvt Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA SRz NodesA SymDriveA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ HMLib.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_ASplit () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.syscall_effect_accesses"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.nret"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_nil"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.mmap_anon_args"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.mmap_errnos"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.errno_ret"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.atop_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.mmap_fixrw_args"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_destroyed"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_outcome"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.mmap_norep_args"; "LinuxProcessSemantics.LinuxProcessSem.State.ENOMEM"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.norep_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinv.kinv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma t_alt2_absorb_l : forall A B : TSet, t_eq (t_alt2 A (t_alt2 A B)) (t_alt2 A B).
Proof. intros A B tr. unfold t_alt2. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_sys2 : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "Pms,$0.Pmo,$1.Px8,(2.&40.)PA,$3.PTB,$3.PPA,P,$4.P,$1.SpPPB,P,$4.P,$1.SpP,(5.(6.(2.&40.))(7.R7.)(8.(2.&40.)R5.))P,(5.(6.(2.&40.))(9.R7.)(:.(2.&40.)))P,Peff,$4.Pmo',$1.Pevs,(;.$<.)P,(=.(>.Vsegs,R<.R:.)R;.(?.$4.R3.R2.R1.))(10.(5.(;.$<.)R2.(11.$<.))(10.(5.(6.(2.&40.))(9.R3.)(:.(2.&40.)))(10.(5.(;.(12.(2.&40.)$13.))(14.R4.)(11.(12.(2.&40.)$13.)))(15.A2.R8.R4.R3.A2.R7.R4.R3.))))P,(16.(=.(>.Vsegs,R:.R8.)R9.(17.$4.)))P,(18.$4.Leff,$4.(18.$1.Lmo',$1.(10.(=.(>.Vsegs,R=.R;.)R<.(?.$4.R2.R1.(11.$<.)))A2.R8.R2.R1.)))P,(18.$4.Leff,$4.(18.$1.Lmo',$1.(10.(=.(>.Vsegs,R>.R<.)R=.(?.$4.R2.R1.(11.$<.)))A2.R8.R2.R1.)))P,Peff,$4.Pmo',$1.P,(=.(>.Vsegs,R?.R=.)R>.(?.$4.R2.R1.(11.$<.)))P,A2.R;.R3.R2.(19.Vsegs,(1:.(1;.R11.R4.)R3.)R>.)P,Peff,$4.Pmo',$1.P,(=.(>.Vsegs,R10.R>.)R?.(?.$4.R2.R1.(11.$<.)))P,A2.R;.R3.R2.(19.Vsegs,(1:.(1;.R12.R4.)R3.)R>.)(19.Vsegs,(1:.R?.R>.)(1<.R<.R;.))")
(* [comment removed for export] *).
Proof.
  (intros ms mo x8 A TB PA PB Hsvc Hh HINV HU dd_H; ddestruct dd_H as (effa & moa & Hsa & HPa); intros dd_H; ddestruct dd_H as (effb & mob & Hsb & HPb); intros HA HB).
  set (IA := { p : SyscallEffect * Model | syscall_spec (sys_input segs ms x8) mo (Ok (fst p) (snd p) []) /\ PA (fst p) (snd p) }).
  set (IB := { p : SyscallEffect * Model | syscall_spec (sys_input segs ms x8) mo (Ok (fst p) (snd p) []) /\ PB (fst p) (snd p) }).
  set (nx := fun i : IA + IB => match i with
                                 | inl p => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p))
                                 | inr p => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p)) end).
  apply (srzJ_alt2 segs (mkCfg ms mo) IA IB nx A TB (exist _ (effa, moa) (conj Hsa HPa)) (exist _ (effb, mob) (conj Hsb HPb))).
  - split.
    + intros [[[eff mo'] [Hs HP]]|[[eff mo'] [Hs HP]]]; cbn in Hs, HP |- *;
        (destruct (HINV _ _ _ Hs) as (_ & Hh' & Hacc & _); unfold nret;
         eapply sstep_syscall; [exact Hh| exact Hsvc| exact Hs| exact Hh'| rewrite Hacc; apply materialize_nil]).
    + intros e st Hs. destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hs)
        as [(eff & mo' & mo'' & Hsp & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hsp & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & ->) | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
      * destruct (HINV _ _ _ Hsp) as (-> & _ & Hacc & HP). rewrite Hacc, materialize_nil in Hm. injection Hm as <-.
        destruct HP as [HP|HP]; [exists (inl (exist _ (eff, mo') (conj Hsp HP)))| exists (inr (exist _ (eff, mo') (conj Hsp HP)))]; split; reflexivity.
      * exfalso. destruct (HINV _ _ _ Hsp) as (_ & _ & Hacc & _). rewrite Hacc, materialize_nil in Hm. discriminate.
      * exfalso. destruct (HINV _ _ _ Hsp) as (_ & Hh2 & _). congruence.
      * exfalso. destruct (HINV _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
      * exfalso. exact (HU Hsp).
  - (intros dd_H; ddestruct dd_H as [[eff mo'] [Hs HP]]). cbn in Hs, HP |- *. exact (HA _ _ Hs HP).
  - (intros dd_H; ddestruct dd_H as [[eff mo'] [Hs HP]]). cbn in Hs, HP |- *. exact (HB _ _ Hs HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_sys3 : forall ms mo x8 (A TB : TSet) (PN PA PB : SyscallEffect -> Model -> Prop),
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall eff mo' evs, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) ->
      evs = [] /\ m_halted mo' = None /\ syscall_effect_accesses eff = [] /\ (PN eff mo' \/ PA eff mo' \/ PB eff mo')) ->
  (~ syscall_spec (sys_input segs ms x8) mo Unmodeled) ->
  (exists eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) /\ PA eff mo') ->
  (exists eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) /\ PB eff mo') ->
  (forall eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) -> PN eff mo' ->
      srealizesJ0 segs (mkCfg (nret ms eff) mo') t_nil /\ spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) mo eff) ->
  (forall eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) -> PA eff mo' -> srealizesJ segs (mkCfg (nret ms eff) mo') A) ->
  (forall eff mo', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' []) -> PB eff mo' -> srealizesJ segs (mkCfg (nret ms eff) mo') TB) ->
  srealizesJ segs (mkCfg ms mo) (t_alt2 A TB).
(* [comment removed for export] *)
Proof.
  (intros ms mo x8 A TB PN PA PB Hsvc Hh HINV HU dd_H; ddestruct dd_H as (effa & moa & Hsa & HPa); intros dd_H; ddestruct dd_H as (effb & mob & Hsb & HPb); intros HN HA HB).
  set (IN := { p : SyscallEffect * Model | syscall_spec (sys_input segs ms x8) mo (Ok (fst p) (snd p) []) /\ PN (fst p) (snd p) }).
  set (IA := { p : SyscallEffect * Model | syscall_spec (sys_input segs ms x8) mo (Ok (fst p) (snd p) []) /\ PA (fst p) (snd p) }).
  set (IB := { p : SyscallEffect * Model | syscall_spec (sys_input segs ms x8) mo (Ok (fst p) (snd p) []) /\ PB (fst p) (snd p) }).
  set (nx := fun i : IN + (IA + IB) => match i with
                                        | inl p => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p))
                                        | inr (inl p) => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p))
                                        | inr (inr p) => mkCfg (nret ms (fst (proj1_sig p))) (snd (proj1_sig p)) end).
  set (T := fun i : IN + (IA + IB) => match i with inl _ => t_nil | inr (inl _) => A | inr (inr _) => TB end).
  assert (HA0 : A []) by (eapply (srzJ_nonempty segs); exact (HA _ _ Hsa HPa)).
  assert (HB0 : TB []) by (eapply (srzJ_nonempty segs); exact (HB _ _ Hsb HPb)).
  apply (srzJ_conseq segs _ (t_alt (fun i => t_emit [] (T i)))).
  - apply (srzJ_node_sp segs (mkCfg ms mo) _ (fun _ => []) nx T (inr (inl (exist _ (effa, moa) (conj Hsa HPa))))).
    + split.
      * intros [[[eff mo'] [Hs HP]]|[[[eff mo'] [Hs HP]]|[[eff mo'] [Hs HP]]]]; cbn in Hs, HP |- *;
          (destruct (HINV _ _ _ Hs) as (_ & Hh' & Hacc & _); unfold nret;
           eapply sstep_syscall; [exact Hh| exact Hsvc| exact Hs| exact Hh'| rewrite Hacc; apply materialize_nil]).
      * intros e st Hs. destruct (sstep_svc_inv segs _ _ _ _ _ Hsvc Hs)
          as [(eff & mo' & mo'' & Hsp & Hh' & Hm & ->) | [(eff & mo' & evs0 & Hsp & Hh' & Hm & -> & ->) | [(eff & mo' & evs0 & code & Hsp & Hh' & -> & ->) | [(eff & mo' & evs0 & sig & Hsp & Hk & -> & ->) | (Hsp & -> & ->)]]]].
        -- destruct (HINV _ _ _ Hsp) as (-> & _ & Hacc & HP). rewrite Hacc, materialize_nil in Hm. injection Hm as <-.
           destruct HP as [HP|[HP|HP]];
             [ exists (inl (exist _ (eff, mo') (conj Hsp HP)))
             | exists (inr (inl (exist _ (eff, mo') (conj Hsp HP))))
             | exists (inr (inr (exist _ (eff, mo') (conj Hsp HP))))]; split; reflexivity.
        -- exfalso. destruct (HINV _ _ _ Hsp) as (_ & _ & Hacc & _). rewrite Hacc, materialize_nil in Hm. discriminate.
        -- exfalso. destruct (HINV _ _ _ Hsp) as (_ & Hh2 & _). congruence.
        -- exfalso. destruct (HINV _ _ _ Hsp) as (_ & Hh2 & _). rewrite (m_killed_of_m_halted_none _ Hh2) in Hk. discriminate.
        -- exfalso. exact (HU Hsp).
    + intros [[[eff mo'] [Hs HP]]|[[[eff mo'] [Hs HP]]|[[eff mo'] [Hs HP]]]]; cbn in Hs, HP |- *;
        [| left; exact (HA _ _ Hs HP)| left; exact (HB _ _ Hs HP)].
      (* [comment removed for export] *)
      right. destruct (HN _ _ Hs HP) as [H0 SR]. split; [exact H0|].
      unfold nret. eapply spurious_fo_excusedJ; [exact Hsvc| exact SR].
  - intros tr. unfold t_alt2. split.
    + (intros dd_H; ddestruct dd_H as [[p|[p|p]] Hi]); cbn in Hi.
      * left. apply (proj1 (t_emit_nil_eq t_nil eq_refl tr)) in Hi. rewrite Hi. exact HA0.
      * left. exact (proj1 (t_emit_nil_eq A HA0 tr) Hi).
      * right. exact (proj1 (t_emit_nil_eq TB HB0 tr) Hi).
    + intros [H|H];
        [ exists (inr (inl (exist _ (effa, moa) (conj Hsa HPa))))| exists (inr (inr (exist _ (effb, mob) (conj Hsb HPb))))]; cbn;
        [ exact (proj2 (t_emit_nil_eq A HA0 tr) H)| exact (proj2 (t_emit_nil_eq TB HB0 tr) H)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_anon_refuse_spec : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "Pms,$0.Px8,(2.&40.)Pmo,$1.PnZ,$1>.Pflags,$1>.Pe,$1>.P,(5.$1>.(1?.&40.R5.)+=>.)P,(20.R7.R4.R3.)P,(21.$1>.R3.$22.)(=.(>.Vsegs,R9.R8.)R7.(?.$4.(23.(24.R4.)(11.(12.(2.&40.)(;.(2.&8.))))(11.(12.(2.&40.)(2.&40.)))(11.(12.(2.&40.)(2.&40.)))(11.$25.)(11.(12.(2.&40.)$13.)))R7.(11.$<.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo nZ flags e Hno HA He.
  dpose (anon_gates ms nZ flags HA) as (Ga & Gb & G0 & G1).
  apply check_syscall_ok_iff. rewrite (mmap_check segs ms x8 mo _ Hno).
  unfold check_mmap. rewrite Ga, Gb, G0, G1. cbn [negb]. cbv zeta beta iota.
  replace (errno_ret_in mmap_errnos (errno_ret e)) with true; [reflexivity|].
  symmetry. destruct He as [<-|[]]. vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma srzJ_mmap_anon_split : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "PR,(26.&5.(2.&40.))PF,(26.&5.(2.&40.))Ppc,(2.&40.)Pfc,(2.&20.)Prv,(6.(2.&40.))Pm,P,(2.&40.)(6.(2.&8.))Pmo,$1.PnZ,$1>.Pflags,$1>.PA,$3.PTB,$3.Zms,$0.(27.R;.R:.R9.(28.&40.+=>.)R8.R7.R6.(29.Vsegs,))P,(5.(6.(2.&40.))(9.R6.)(:.(2.&40.)))P,(2:.VhAR,(2;.(2<.R7.)))P,(20.R3.R7.R6.)P,(18.(2.&40.)La,(2.&40.)(2=.VhAR,R8.R9.R:.R1.))P,Pe,$1>.P,(21.$1>.R1.$22.)(19.Vsegs,(1:.(1;.R7.(23.(24.R2.)(11.(12.(2.&40.)(;.(2.&8.))))(11.(12.(2.&40.)(2.&40.)))(11.(12.(2.&40.)(2.&40.)))(11.$25.)(11.(12.(2.&40.)$13.))))R<.)R9.)P,Pa,(2.&40.)P,(5.$1>.(2>.(1?.&40.R1.)+1000.)=)P,(2?.=(1?.&40.R2.))P,(30.(31.(1?.&40.R3.)R=.)(32.VhAR,))P,(5.$33.(34.(35.(12.(2.&40.)(2.&40.))(36.(2<.R?.))(37.(2<.R?.)))R4.(28.&40.R>.))$38.)(19.Vsegs,(1:.(1;.R;.(23.R5.(11.(12.(2.&40.)(;.(2.&8.))))(39.(12.(2.&40.)(2.&40.))(3:.(2.&40.)(2.&40.)R5.(28.&40.R?.))(11.(12.(2.&40.)(2.&40.))))(11.(12.(2.&40.)(2.&40.)))(11.$25.)(11.(12.(2.&40.)$13.))))(3;.R>.R5.R?.R10.))R<.)(19.Vsegs,(1:.R7.R<.)(1<.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros R F pc fc rv m mo nZ flags A TB ms Hh ATOP HA (aw & GW) HR HG.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  apply (srzJ_sys2 ms mo (Z_to_bv 64 222) A TB
           (fun eff mo' => exists e, In e mmap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [] [] [] /\ mo' = mo)
           (fun eff mo' => exists a : word, bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= ACEIL
                              /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 nZ) = true
                              /\ eff = mkEffect a [] [(a, Z_to_bv 64 nZ)] /\ mo' = anon_grant flags a nZ mo)).
  - reflexivity.
  - exact Hh.
  - intros eff mo' evs Hs.
    destruct (mmap_anon_inv segs ms (Z_to_bv 64 222) mo nZ flags eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    split; [reflexivity|]. destruct OUT as [e HIn | a AL A0 CE RF].
    + split; [exact Hh|]. split; [reflexivity|]. left. exists e. repeat split; auto.
    + split; [rewrite halted_anon_grant; exact Hh|]. split; [reflexivity|]. right. exists a. repeat split; auto.
  - eapply (mmap_anon_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
  - dexists (mkEffectU (errno_ret ENOMEM) [] [] [] [] []), mo. split.
    + apply (mmap_anon_refuse_spec ms (Z_to_bv 64 222) mo nZ flags ENOMEM E222 HA). left. reflexivity.
    + exists ENOMEM. repeat split; auto. left. reflexivity.
  - dexists (mkEffect aw [] [(aw, Z_to_bv 64 nZ)]), (anon_grant flags aw nZ mo). split.
    + exact (mmap_anon_grant_spec segs ms (Z_to_bv 64 222) mo nZ flags aw E222 HA ATOP GW).
    + ddestruct GW as (AL & A0 & FL & CE & RF & BU). exists aw. repeat split; auto.
  - (intros eff mo' _ dd_H; ddestruct dd_H as (e & He & -> & ->)). exact (HR e He).
  - (intros eff mo' _ dd_H; ddestruct dd_H as (a & AL & A0 & CE & RF & -> & ->)). exact (HG a AL A0 CE RF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_fixrw_destroy_spec : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "Pms,$0.Px8,(2.&40.)Pmo,$1.Paddr,$1>.PnZ,$1>.Pflags,$1>.Pe,$1>.P,(5.$1>.(1?.&40.R6.)+=>.)P,(3<.VhAR,R8.R5.R4.R3.)P,(2:.VhAR,(2;.(2<.R7.)))P,(5.$33.(34.(36.(2<.R8.))(28.&40.R7.)(28.&40.R6.))$38.)P,(5.$33.(3=.(37.(2<.R9.))(28.&40.R8.)(28.&40.R7.))$38.)P,(21.$1>.R6.$22.)(=.(>.Vsegs,R=.R<.)R;.(?.$4.(23.(24.R7.)(11.(12.(2.&40.)(;.(2.&8.))))(11.(12.(2.&40.)(2.&40.)))(39.(12.(2.&40.)(2.&40.))(3:.(2.&40.)(2.&40.)(28.&40.R:.)(28.&40.R9.))(11.(12.(2.&40.)(2.&40.))))(11.$25.)(11.(12.(2.&40.)$13.)))(3>.R:.R9.R;.)(11.$<.)))")
(* [comment removed for export] *).
Proof.
  intros ms x8 mo addr nZ flags e Hno HA ATOP RF MC He. pose proof aceil_bounds as AC.
  dpose (fixrw_gates ms addr nZ flags HA) as (Ga & Gb & G0 & G1 & G2 & G3 & G4).
  dpose HA as (H10 & Hn & H11 & H12 & H13 & H14 & H15 & AL & A0 & N0 & CE & FL).
  assert (ER : errno_ret_in mmap_errnos (errno_ret e) = true) by (destruct He as [<-|[]]; vm_compute; reflexivity).
  apply check_syscall_ok_iff. rewrite (mmap_check segs _ _ _ _ Hno).
  unfold check_mmap. rewrite Ga, Gb, G0, G1, G2, G3, G4. cbn [negb]. cbv zeta.
  rewrite H10. rewrite !unsigned_lit by lia. rewrite Hn.
  destruct (Z.leb_spec0 two_pow_64 (addr + nZ)) as [L|L]; [unfold two_pow_64 in L; lia|].
  destruct (Z.leb_spec0 (addr + nZ) (alloc_top (m_vmmaps mo))) as [L2|L2]; [| pose proof (atop_ok_le _ ATOP); lia]. cbn [negb].
  change page_size with 4096. rewrite (proj2 (Z.eqb_eq _ _) AL). cbn [negb].
  destruct (Z.ltb_spec0 0 addr) as [L3|L3]; [|lia]. cbn [negb].
  rewrite RF, MC. cbv beta iota. rewrite ER. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_mmap_fixrw_split3 : forall R F pc fc rv m mo addr nZ flags (A TB : TSet),
  let ms := MSsvc R F pc (Z_to_bv 64 222) fc rv m (seg_rom segs) in
  m_halted mo = None -> atop_ok (alloc_top (m_vmmaps mo)) -> mmap_fixrw_args ms addr nZ flags ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  fixrw_grantable flags addr nZ mo ->
  (forall e, In e mmap_errnos -> srealizesJ0 segs (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [] [] [])) mo) t_nil) ->
  (forall e, In e mmap_errnos ->
      srealizesJ segs (mkCfg (nret ms (mkEffectU (errno_ret e) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [])) (fixrw_destroyed addr nZ mo)) A) ->
  (forall mo', fixrw_outcome flags addr nZ mo (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]) mo' ->
      srealizesJ segs (mkCfg (nret ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) mo') TB) ->
  srealizesJ segs (mkCfg ms mo) (t_alt2 A TB).
(* [comment removed for export] *)
Proof.
  intros R F pc fc rv m mo addr nZ flags A TB ms Hh ATOP HA RF MC GR HN HD HG.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  ddestruct (mmap_fixrw_grant_spec segs ms (Z_to_bv 64 222) mo addr nZ flags E222 HA ATOP RF (or_introl MC) GR) as (mog & OUTg & Hhg & Hsg).
  assert (NRg : errno_ret_in mmap_errnos (eff_ret (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)])) = false).
  { cbn [eff_ret]. dpose HA as (_ & _ & _ & _ & _ & _ & _ & AL & A0 & N0 & CE & _). aceilb.
    apply (grant_ret_not_errno (Z_to_bv 64 addr) nZ); [lia|]. rewrite unsigned_lit by lia. exact CE. }
  apply (srzJ_sys3 ms mo (Z_to_bv 64 222) A TB
           (fun eff mo' => exists e, In e mmap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [] [] [] /\ mo' = mo)
           (fun eff mo' => exists e, In e mmap_errnos /\ eff = mkEffectU (errno_ret e) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [] /\ mo' = fixrw_destroyed addr nZ mo)
           (fun eff mo' => eff = mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] /\ fixrw_outcome flags addr nZ mo eff mo')).
  - reflexivity.
  - exact Hh.
  - intros eff mo' evs Hs.
    destruct (mmap_fixrw_inv segs ms (Z_to_bv 64 222) mo addr nZ flags eff mo' evs E222 HA ATOP RF (or_introl MC) Hs) as [-> OUT].
    split; [reflexivity|]. pose proof OUT as OUT'. destruct OUT as [e HIn | e HIn MC' | MC' | FR].
    + split; [exact Hh|]. split; [reflexivity|]. left. exists e. split; [exact HIn|]. split; reflexivity.
    + split; [rewrite halted_fixrw_destroyed; exact Hh|]. split; [reflexivity|]. right. left. exists e. split; [exact HIn|]. split; reflexivity.
    + split; [rewrite halted_fixrw_commit; exact Hh|]. split; [reflexivity|]. right. right. split; [reflexivity| exact OUT'].
    + split; [rewrite halted_fixrw_fresh; exact Hh|]. split; [reflexivity|]. right. right. split; [reflexivity| exact OUT'].
  - eapply (mmap_fixrw_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
  - dexists (mkEffectU (errno_ret ENOMEM) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []), (fixrw_destroyed addr nZ mo). split.
    + apply (mmap_fixrw_destroy_spec ms (Z_to_bv 64 222) mo addr nZ flags ENOMEM E222 HA ATOP RF MC). left. reflexivity.
    + exists ENOMEM. split; [left; reflexivity|]. split; reflexivity.
  - dexists (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)]), mog. split; [exact Hsg|]. split; [reflexivity| exact OUTg].
  - (intros eff mo' _ dd_H; ddestruct dd_H as (e & He & -> & ->)). split; [exact (HN e He)|].
    apply (mmap_refusal_spurious segs ms (Z_to_bv 64 222) mo _ _ _ _ E222 Hsg NRg). cbn [eff_ret]. apply errno_ret_in_intro. exact He.
  - (intros eff mo' _ dd_H; ddestruct dd_H as (e & He & -> & ->)). exact (HD e He).
  - intros eff mo' _ (-> & OUT). exact (HG mo' OUT).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma srzJ_mmap_norep_hole_split : forall R F pc fc rv m mo addr nZ (A : TSet),
  let ms := MSsvc R F pc (Z_to_bv 64 222) fc rv m (seg_rom segs) in
  m_halted mo = None -> atop_ok (alloc_top (m_vmmaps mo)) -> mmap_norep_args ms addr nZ ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) = true ->
  srealizesJ0 segs (mkCfg (nret ms (mkEffectU (errno_ret ENOMEM) [] [] [] [] [])) mo) t_nil ->
  srealizesJ segs (mkCfg (nret ms (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [])) (norep_grant addr nZ mo)) A ->
  srealizesJ segs (mkCfg ms mo) A.
(* [comment removed for export] *)
Proof.
  intros R F pc fc rv m mo addr nZ A ms Hh ATOP HA FR HN HG.
  assert (E222 : bv_unsigned (Z_to_bv 64 222) = 222) by (vm_compute; reflexivity).
  pose proof (mmap_norep_grant_spec segs ms (Z_to_bv 64 222) mo addr nZ E222 HA ATOP FR) as Hsg.
  assert (NRg : errno_ret_in mmap_errnos (eff_ret (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [])) = false).
  { cbn [eff_ret]. dpose HA as (_ & _ & _ & _ & _ & _ & _ & AL & A0 & N0 & CE). aceilb.
    apply (grant_ret_not_errno (Z_to_bv 64 addr) nZ); [lia|]. rewrite unsigned_lit by lia. exact CE. }
  apply (srzJ_conseq segs _ (t_alt2 A A)); [| intros tr; unfold t_alt2; tauto].
  apply (srzJ_sys3 ms mo (Z_to_bv 64 222) A A
           (fun eff mo' => eff = mkEffectU (errno_ret ENOMEM) [] [] [] [] [] /\ mo' = mo)
           (fun eff mo' => eff = mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [] /\ mo' = norep_grant addr nZ mo)
           (fun eff mo' => eff = mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] [] /\ mo' = norep_grant addr nZ mo)).
  - reflexivity.
  - exact Hh.
  - intros eff mo' evs Hs.
    destruct (mmap_norep_inv segs ms (Z_to_bv 64 222) mo addr nZ eff mo' evs E222 HA ATOP Hs) as [-> OUT].
    split; [reflexivity|]. destruct OUT as [| OCC | FR'].
    + split; [exact Hh|]. split; [reflexivity|]. left. split; reflexivity.
    + exfalso. rewrite FR in OCC. discriminate OCC.
    + split; [rewrite halted_norep_grant; exact Hh|]. split; [reflexivity|]. right. left. split; reflexivity.
  - eapply (mmap_norep_no_unmodeled segs ms (Z_to_bv 64 222)); eauto.
  - dexists (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []), (norep_grant addr nZ mo). split; [exact Hsg| split; reflexivity].
  - dexists (mkEffectU (Z_to_bv 64 addr) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 nZ)] [] []), (norep_grant addr nZ mo). split; [exact Hsg| split; reflexivity].
  - intros eff mo' _ (-> & ->). split; [exact HN|].
    apply (mmap_refusal_spurious segs ms (Z_to_bv 64 222) mo _ _ _ _ E222 Hsg NRg). cbn [eff_ret]. apply errno_ret_in_intro. left. reflexivity.
  - intros eff mo' _ (-> & ->). exact HG.
  - intros eff mo' _ (-> & ->). exact HG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma evtA_srzJ_K : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "PL,$44.PCS,P,$1>.SpPK,P,$1.SpPP,P,$0.SpPT,$3.Pms,$0.Pmo,$1.P,(45.VhAR,R7.R6.R5.)P,A1.R6.R2.P,(46.Vsegs,R9.R8.R6.R4.)P,Pms',$0.Pmo',$1.P,A1.R9.R2.P,A1.R;.R2.P,(47.R8.R3.)(19.Vsegs,(1:.R5.R4.)R;.)(19.Vsegs,(1:.R6.R5.)R7.)")
(* [comment removed for export] *).
Proof.
  intros L CS K P T ms mo KL HK EV CONT.
  eapply (rz_evtA_K segs L CS K (ki_halted KL) (ki_mat KL) P ms mo T HK EV). exact CONT.
Qed.

(* [comment removed for export] *)
Hypothesis WVH : forall (m : word -> option byte) (x : word), JF <= bv_unsigned x -> wview segs m x = m x.
#[using="WVH"] Lemma evtA_srzJ_KJ0 : ltac2:(CDefT.buildp (gd_tbl_ASplit ()) "PL,$44.PCS,P,$1>.SpPK,P,$1.SpPP,P,$0.SpPT,$3.Pms,$0.Pmo,$1.P,(45.VhAR,R7.R6.R5.)P,A1.R6.R2.P,(48.(49.R4.)R3.)P,(46.Vsegs,R:.R9.R7.R5.)P,Pms',$0.Pmo',$1.P,A1.R:.R2.P,A1.R<.R2.P,(47.R9.R3.)P,(48.(49.R5.)R4.)(19.Vsegs,(1:.R6.R5.)R=.)(19.Vsegs,(1:.R7.R6.)R8.)")
(* [comment removed for export] *).
Proof.
  intros L CS K P T ms mo KL HK HJ EV CONT.
  eapply (evtA_srzJ_K L CS K _ T ms mo KL HK (evtA_nwmono segs L CS P ms EV)).
  cbn beta. intros ms' mo' [HP NW] HK' MM. apply CONT; try assumption.
  apply (J_nwmono segs WVH _ _ _ NW). eapply J_mat; eauto.
Qed.

End WithSegs.

(* [comment removed for export] *)
Definition evtA_srzJ_KJ (L : asan_layout) := evtA_srzJ_KJ0 asegs wview_high L.
End ARUN_1.
