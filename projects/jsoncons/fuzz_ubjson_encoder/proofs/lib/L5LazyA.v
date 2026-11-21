(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct AsanAcctShape HeapIface HeapIfaceA L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_L5LazyA () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib7Numbers7BinNums8positive01I47Corelib4Init9Datatypes6option00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct9mrestrictC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K47Corelib4Init5Logic2eq01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct;munrestrictC13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic6eq_symC46Stdlib5LogicHFunctionalExtensionalityIfunctional_extensionalityK47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic3and00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>H_off_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>wx_segs_nowrapC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:lazy_coverC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4A_wfC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct4MInv00C13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6CatSim6msteps00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctEsame_but_materializedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct8restrictC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ=restrict_mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct6hcleanC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct:unrestrictC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ?unrestrict_mkstC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib=AsanAcctShapeGsrz_msteps_restricted_TC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List4inclC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct>lazy_cover_mkHC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA4ahidC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct<segs_below_bC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9page_baseC4ELinuxProcessSemantics?LinuxProcessSem5State>page_in_rangesC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct=page_allowedbC13~~~C47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes9andb_propK47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcctHfind_segment1_none_aboveC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem5StateAm_vm_materializedC4ELinuxProcessSemantics?LinuxProcessSem5State?with_vm_backingK4ELinuxProcessSemantics?LinuxProcessSem5State5Model01K4ELinuxProcessSemantics?LinuxProcessSem5State7VmState01I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State7VmState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9TimeState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8AsanAcct3mkHC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7L5LazyA4L5LZ8sbm_lazyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceA8model_rtC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State4m_vmC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State6m_time".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5LZ.
Section WithSegs.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Lemma restrict_mkst (fx : FPState) H R pc M :
  restrict H (@mkst fx R pc M (seg_rom segs)) = @mkst fx R pc (mrestrict H M) (seg_rom segs).
Proof. reflexivity. Qed.
Lemma unrestrict_mkst (fx fx' : FPState) H R pc M R' pc' M' :
  unrestrict H (ms_mem (@mkst fx R pc M (seg_rom segs))) (@mkst fx' R' pc' M' (seg_rom segs))
  = @mkst fx' R' pc' (munrestrict H M M') (seg_rom segs).
Proof. reflexivity. Qed.


(* [comment removed for export] *)
Lemma mrestrict_of_munrestrict H M M' :
  (forall a, H a = true -> M' a = None) -> mrestrict H (munrestrict H M M') = M'.
Proof.
  intros Hc. apply functional_extensionality. intros a. unfold mrestrict, munrestrict.
  destruct (H a) eqn:E. symmetry; apply Hc; exact E. reflexivity.
Qed.
Lemma munrestrict_hidden H M M' a : H a = true -> munrestrict H M M' a = M a.
Proof. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma munrestrict_visible H M M' a : H a = false -> munrestrict H M M' a = M' a.
Proof. intros E. unfold munrestrict. rewrite E. reflexivity. Qed.
Lemma mrestrict_visible' H M a : H a = false -> mrestrict H M a = M a.
Proof. intros E. unfold mrestrict. rewrite E. reflexivity. Qed.
(* [comment removed for export] *)
Lemma mrestrict_agree_on (H H' : word -> bool) (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a, P a -> H (Z_to_bv 64 a) = false /\ H' (Z_to_bv 64 a) = false) ->
  (forall a, P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  forall a, P a -> mrestrict H' M' (Z_to_bv 64 a) = mrestrict H M (Z_to_bv 64 a).
Proof.
  intros HV HM a Ha. destruct (HV a Ha) as [E E']. unfold mrestrict. rewrite E, E'. apply HM. exact Ha.
Qed.

(* [comment removed for export] *)
Theorem cps_of_msteps_lazy (H : word -> bool) (A : list (Z * Z))
        (fx fx' : FPState) R pc M R' pc' (M1v : word -> option byte) (model : Model) K :
  H_off_segments segs H -> wx_segs_nowrap segs ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
  msteps segs (@mkst fx R pc (mrestrict H M) (seg_rom segs)) (@mkst fx' R' pc' M1v (seg_rom segs)) ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
       (forall a, H a = true -> M1v a = None) ->
       srealizes segs SCFG (mkCfg (@mkst fx' R' pc' (munrestrict H M M1v) (seg_rom segs)) model') K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof.
  intros HH Hwx HL HA HI Hh MS HK.
  rewrite <- (restrict_mkst fx H R pc M) in MS.
  apply (srz_msteps_restricted_T segs SCFG H HH Hwx A _ _ model K HL HA HI Hh MS).
  intros model' HI' HS HC. rewrite (unrestrict_mkst fx fx') . apply (HK model' HI' HS).
  intros a Ha. exact (HC a Ha).
Qed.

(* [comment removed for export] *)
Lemma lazy_cover_ahid A model : lazy_cover (ahid A model) (m_vm_lazy model) A.
Proof. unfold ahid. apply lazy_cover_mkH. intros r Hr; exact Hr. Qed.

(* [comment removed for export] *)
Lemma H_off_segments_ahid A model top :
  segs_below_b segs top = true ->
  (forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true -> top <= bv_unsigned w) ->
  H_off_segments segs (ahid A model).
Proof.
  intros Hb Hhi a Ha. unfold ahid, mkH in Ha. apply andb_prop in Ha as [Hp _].
  apply (find_segment1_none_above segs top). exact Hb. apply Hhi. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma sbm_halted m m' : same_but_materialized m m' -> m_halted m' = m_halted m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_lazy m m' : same_but_materialized m m' -> m_vm_lazy m' = m_vm_lazy m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_vmmaps m m' : same_but_materialized m m' -> m_vmmaps m' = m_vmmaps m.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma sbm_ahid A m m' : same_but_materialized m m' -> ahid A m' = ahid A m.
Proof. intros Hs. unfold ahid. rewrite (sbm_lazy m m' Hs). reflexivity. Qed.
Lemma sbm_model_rt m m' : same_but_materialized m m' -> model_rt m m'.
Proof. intros ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma model_rt_trans m1 m2 m3 : model_rt m1 m2 -> model_rt m2 m3 -> model_rt m1 m3.
Proof. unfold model_rt. intros -> ->. destruct m1; reflexivity. Qed.
Lemma model_rt_halted m m' : model_rt m m' -> m_halted m' = m_halted m.
Proof. intros ->. destruct m; reflexivity. Qed.

End WithSegs.
End L5LZ.
