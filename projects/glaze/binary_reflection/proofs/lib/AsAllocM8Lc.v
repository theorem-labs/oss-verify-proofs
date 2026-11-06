(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8v.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Lemma pf_cv_mrestrict : forall (Hd : word -> bool) M top au csz i,
  0 <= top - 4 * Z.of_nat i -> top < 2 ^ 64 -> hid_off Hd (top - 4 * Z.of_nat i) (4 * Z.of_nat i) ->
  pf_cv (mrestrict Hd M) top au csz i = mrestrict Hd (pf_cv M top au csz i).
Proof using.
  induction i as [|i IH]; intros H0 H1 Hh; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [pf_cv] in G in change_no_check G' end).
  rewrite IH by (first [lia | eapply hid_off_sub; [exact Hh | lia | lia]]).
  apply wbytes_mrestrict; rewrite length_N_to_le_bytes, u_Z2bv by lia; [lia | eapply hid_off_sub; [exact Hh | lia | lia]].
Qed.

Lemma pf_mc_outside : forall M RIz top au csz nf newn (x : word),
  0 <= newn -> 0 <= top - 4 * newn -> top < 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  (U x < top - 4 * newn \/ top <= U x) -> (U x < RIz \/ RIz + 128 <= U x) ->
  pf_mc M RIz top au csz nf newn x = M x.
Proof using.
  intros M RIz top au csz nf newn x N0 H0 H1 R0 R1 X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end).
  rewrite MemsetLibF.MemSplit.wbytes_outside; [ | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
  repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia]).
  apply pf_cv_outside; rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma pf_mc_mrestrict : forall (Hd : word -> bool) M RIz top au csz nf newn,
  0 <= newn -> 0 <= top - 4 * newn -> top < 2 ^ 64 -> 0 <= RIz -> RIz + 128 <= 2 ^ 64 ->
  hid_off Hd (top - 4 * newn) (4 * newn) -> hid_off Hd RIz 128 ->
  pf_mc (mrestrict Hd M) RIz top au csz nf newn = mrestrict Hd (pf_mc M RIz top au csz nf newn).
Proof using.
  intros Hd M RIz top au csz nf newn N0 H0 H1 R0 R1 O1 O2. (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end).
  rewrite pf_cv_mrestrict by (rewrite ?Z2Nat.id by lia; first [lia | exact O1]).
  rewrite !wbytes_mrestrict; [reflexivity | | | | | |];
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
    first [lia | eapply hid_off_sub; [exact O2 | lia | lia]].
Qed.

Section LIFTS.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem pf_carve_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (M rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (RIz SPB c au mu nf : Z) (Qok Qf : config -> Prop),
    let newn := (mu - au) / csize c in
    let FAB := SPB + c * 2 ^ 32 + 0xE0000000 in
    let top := SPB + c * 2 ^ 32 + 0xE0000000 + 4 * (nf + (mu - au) / csize c) in
    pf_regs sp RIz SPB c regs -> getr regs 10 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 (nf + newn) ->
    getr regs 19 = Z_to_bv 64 newn -> getr regs 20 = Z_to_bv 64 (mu - au) ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> 1 <= c <= 30 ->
    (0 <= au /\ au + csize c <= mu /\ mu <= 0xE0000000) -> (0 <= nf /\ 4 * (nf + (mu - au) / csize c) <= 2 ^ 29) ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64) -> (SPB + 2 ^ 37 <= RIz /\ RIz + 128 <= U sp - 64) ->
    rdn ASEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) -> rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)) ->
    rdn ASEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) -> rdn ASEGS M (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn ASEGS M (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    store_ok ASEGS M (Z_to_bv 64 RIz) 128 = true -> store_ok ASEGS M (Z_to_bv 64 (FAB + 4 * nf)) (Z.to_nat (4 * newn)) = true ->
    rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    hid_off Hd RIz 128 -> hid_off Hd (FAB + 4 * nf) (4 * newn) -> hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        pf_post1 sp ra s0v s1v s2v s3v s4v s5v s6v regs r ->
        katwD ASEGS (mkCfg (mkst r ra (pf_mc M RIz top au (csize c) nf newn) rom) mdlm) Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50f68 : word) M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4v s5v s6v RIz SPB c au mu nf Qok Qf newn FAB top
           HR H10 H9 H19 H20 Hsp Hret Hc Hau Hnf HSPB HRI Rau Rnf Rmu Ram Rmm SOKRI SOKfa Sra Ss0 Ss1 Ss2 Ss3 Ss4 Ss5 Ss6
           HDRI HDfa HDf HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [CS1 CS2].
    assert (N0 : 0 <= newn) by ((lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end); apply Z.div_pos; lia).
    assert (TOPE : top - 4 * newn = FAB + 4 * nf) by ((lazymatch goal with |- ?G => let G' := eval unfold top, FAB, newn in G in change_no_check G' end); lia).
    assert (RIr : forall (k : Z) v, 0 <= k -> k + 8 <= 128 -> rdn ASEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v ->
               rdn ASEGS (mrestrict Hd M) (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]]. }
    assert (SPr : forall (k : Z) v, -64 <= k -> k + 8 <= 0 -> rdn ASEGS M (at_ sp k) 8 = Some v -> rdn ASEGS (mrestrict Hd M) (at_ sp k) 8 = Some v).
    { intros k v K0 K1 Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]]. }
    destruct (pf_carve (mrestrict Hd M) rom sp ra s0v s1v s2v s3v s4v s5v s6v RIz SPB c au mu nf Hsp Hret Hc Hau Hnf HSPB HRI
                (RIr 32 _ ltac:(lia) ltac:(lia) Rau) (RIr 16 _ ltac:(lia) ltac:(lia) Rnf) (RIr 48 _ ltac:(lia) ltac:(lia) Rmu)
                (RIr 40 _ ltac:(lia) ltac:(lia) Ram) (RIr 56 _ ltac:(lia) ltac:(lia) Rmm)) with (regs := regs)
      as (r & RUN & POST).
    - rewrite store_ok_mrestrict; [exact SOKRI | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HDRI].
    - fold newn FAB. rewrite store_ok_mrestrict; [exact SOKfa | rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold FAB in G in change_no_check G' end); lia); rewrite Z2Nat.id by lia; unfold FAB, newn in *; lia
                                       | rewrite u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold FAB in G in change_no_check G' end); lia); rewrite Z2Nat.id by lia; exact HDfa].
    - apply SPr; [lia | lia | exact Sra].
    - apply SPr; [lia | lia | exact Ss0].
    - apply SPr; [lia | lia | exact Ss1].
    - apply SPr; [lia | lia | exact Ss2].
    - apply SPr; [lia | lia | exact Ss3].
    - apply SPr; [lia | lia | exact Ss4].
    - apply SPr; [lia | lia | exact Ss5].
    - apply SPr; [lia | lia | exact Ss6].
    - exact HR.
    - exact H10.
    - exact H9.
    - exact H19.
    - exact H20.
    - assert (TOP1 : 0 <= top - 4 * newn /\ top < 2 ^ 64) by (rewrite TOPE; unfold top, FAB, newn in *; lia).
      assert (HDfa' : hid_off Hd (top - 4 * newn) (4 * newn)) by (rewrite TOPE; exact HDfa).
      assert (HIDSAME : forall a : word, Hd a = true -> pf_mc M RIz top au (csize c) nf newn a = M a).
      { intros a Ha.
        pose proof (hid_true_off Hd a _ _ Ha HDfa') as Z1. pose proof (hid_true_off Hd a _ _ Ha HDRI) as Z2.
        apply pf_mc_outside; [exact N0 | lia | lia | lia | lia | lia | lia]. }
      apply (katwD_msteps_acct ASEGS Hd HOFFSEG WX A (mkst regs (0x50f68 : word) M rom)
               (mkst r ra (mrestrict Hd (pf_mc M RIz top au (csize c) nf newn)) rom) model Qok Qf LC AWF MI HALT).
      { rewrite mk_restrict_mkst.
        rewrite <- (pf_mc_mrestrict Hd M RIz top au (csize c) nf newn N0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HDfa' HDRI).
        exact RUN. }
      intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (0x50f68 : word) M rom)) with M by reflexivity.
      rewrite (mk_munrestrict_same Hd M _ HIDSAME).
      exact (CONT r mdlm SBMm MIm POST).
  Qed.
End LIFTS.
End FPGen.
End AsAllocM8v.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8La.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pf_mc_grows : forall M RIz top au csz nf newn, mem_grows M (pf_mc M RIz top au csz nf newn).
Proof.
  intros. (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply pf_cv_grows.
Qed.

Lemma pf_cv_entry : forall segs M top au csz (n i : nat), (i < n)%nat -> 0 <= top - 4 * Z.of_nat n -> top < 2 ^ 64 ->
  rdn segs (pf_cv M top au csz n) (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1))) 4 = Some (LE4 ((au + Z.of_nat i * csz) / 16)).
Proof.
  intros segs M top au csz n. induction n as [|n IH]; intros i Hi H0 H1; [lia|]. (lazymatch goal with |- ?G => let G' := eval cbn [pf_cv] in G in change_no_check G' end).
  destruct (Nat.eq_dec i n) as [->|NE].
  - apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
  - rewrite rdn_wbytes_out; [apply IH; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                            | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia].
Qed.

Lemma pf_mc_rd : forall segs M RIz top au csz nf newn, 0 <= newn -> 0 <= top - 4 * newn -> top <= RIz -> RIz + 128 <= 2 ^ 64 ->
  rdn segs (pf_mc M RIz top au csz nf newn) (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 (nf + newn)))
  /\ rdn segs (pf_mc M RIz top au csz nf newn) (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 (au + newn * csz)))
  /\ rdn segs (pf_mc M RIz top au csz nf newn) (Z_to_bv 64 (RIz + 68)) 1 = Some [Z_to_bv 8 0]
  /\ (forall i : nat, Z.of_nat i < newn ->
        rdn segs (pf_mc M RIz top au csz nf newn) (Z_to_bv 64 (top - 4 * (Z.of_nat i + 1))) 4 = Some (LE4 ((au + Z.of_nat i * csz) / 16))).
Proof.
  intros segs M RIz top au csz nf newn N0 H0 H1 H2. (lazymatch goal with |- ?G => let G' := eval unfold pf_mc in G in change_no_check G' end).
  Ltac peelw := rewrite rdn_wbytes_out; [ | first [rewrite length_N_to_le_bytes | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end)]; rewrite !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                          | first [rewrite length_N_to_le_bytes | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end)]; rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  split; [|split; [|split]].
  - peelw. peelw. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
  - peelw. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
  - apply (rdn_wbytes_hit segs [Z_to_bv 8 0]). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  - intros i Hi. peelw. peelw. peelw. apply pf_cv_entry; [lia | rewrite Z2Nat.id by lia; lia | lia].
Qed.

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  (* [comment removed for export] *)
  Definition XL (c : Z) (z : Z) : Prop := X z \/ reginfo bt c <= z < reginfo bt c + 8.

  (* [comment removed for export] *)
  Lemma repx_off : forall (Y : Z -> Prop) (M M0 : mem), (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
    forall a : word, ~ Y (U a) -> M a = M0 a.
  Proof using.
    intros Y M M0 D a NY. destruct (decide (M a = M0 a)) as [E | NE]; [exact E|]. exfalso. exact (NY (proj1 (D a NE))).
  Qed.
  Lemma repx_rd : forall (Y : Z -> Prop) (M M0 : mem), (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
    forall (z : Z) (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ Y i) ->
    rdn ASEGS M0 (Z_to_bv 64 z) k = Some v -> rdn ASEGS M (Z_to_bv 64 z) k = Some v.
  Proof using.
    intros Y M M0 D z k v Z0 Z1 OFF Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply (repx_off Y M M0 D). apply OFF. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma repx_wr : forall (Y : Z -> Prop) (M M0 : mem), (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
    forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> writableZ ASEGS M0 lo hi -> writableZ ASEGS M lo hi.
  Proof using.
    intros Y M M0 D lo hi L0 H1 WR i Hi. destruct (WR i Hi) as [W1 W2].
    destruct (decide (M (Z_to_bv 64 i) = M0 (Z_to_bv 64 i))) as [E | NE].
    - split; [rewrite E; exact W1|]. rewrite <- W2. apply store_ok_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. assert (x = Z_to_bv 64 i) as -> by (apply bv_eq; rewrite u_Z2bv by lia; lia). exact E.
    - destruct (D _ NE) as [_ DEF]. split; [exact DEF|].
      apply store_ok_of_all; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
      assert (x = Z_to_bv 64 i) as -> by (apply bv_eq; rewrite u_Z2bv by lia; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M (Z_to_bv 64 i)) as [b|]; [discriminate | exfalso; exact (DEF eq_refl)].
  Qed.
  Lemma writableZ_sok : forall (M : mem) lo hi (a : word) (n : nat), writableZ ASEGS M lo hi -> lo <= U a -> U a + Z.of_nat n <= hi -> hi < 2 ^ 64 ->
    store_ok ASEGS M a n = true.
  Proof using.
    intros M lo hi a n WR L H H1. pose proof (u64_range a). apply store_ok_of_all; [lia|]. intros x Hx.
    destruct (WR (U x) ltac:(lia)) as [DEF _]. rewrite Z_to_bv_bv_unsigned in DEF. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M x); [discriminate | exfalso; exact (DEF eq_refl)].
  Qed.


  (* [comment removed for export] *)
  Lemma repx_step : forall (Y RES FOOT : Z -> Prop) (Rd : Xdec RES) st st' Lc Lc' FF FF' (M M' : mem) mdl mdl',
    RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> FOOT (U a) /\ M' a <> None) ->
    (forall a : word, RES (U a) -> M' a <> None) ->
    (forall M0 M0' : mem, Rep bt st Lc FF M0 mdl ->
        (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
        (forall a : word, M0' a <> M0 a -> (FOOT (U a) \/ RES (U a)) /\ M0' a <> None) ->
        (forall a : word, ~ Y (U a) \/ RES (U a) -> M0' a = M' a) ->
        (forall a : word, M a = M0 a -> M0' a = M' a) ->
        Rep bt st' Lc' FF' M0' mdl') ->
    RepX bt (fun z => Y z /\ ~ RES z) st' Lc' FF' M' mdl'.
  Proof using.
    intros Y RES FOOT Rd st st' Lc Lc' FF FF' M M' mdl mdl' (M0 & R & D) STEPM RDEF STEP.
    set (M0' := fun a : word => if Rd (U a) then M' a else if decide (M a = M0 a) then M' a else M0 a).
    exists M0'. split.
    - apply (STEP M0 M0' R D).
      + intros a Ha. unfold M0' in Ha |- *. destruct (Rd (U a)) as [HR | NR]; [split; [right; exact HR | exact (RDEF a HR)]|].
        destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
        rewrite <- E in Ha. destruct (STEPM a Ha) as [F Dd]. exact (conj (or_introl F) Dd).
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Rd (U a)) as [HR | NR]; [reflexivity|].
        destruct (decide (M a = M0 a)) as [E | NE]; [reflexivity|]. exfalso. destruct Ha as [Ha | Ha]; [exact (Ha (proj1 (D a NE))) | exact (NR Ha)].
      + intros a E. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Rd (U a)); [reflexivity|]. destruct (decide (M a = M0 a)) as [_ | NE]; [reflexivity | exfalso; exact (NE E)].
    - intros a Ha. unfold M0' in Ha. destruct (Rd (U a)) as [HR | NR]; [exfalso; exact (Ha eq_refl)|].
      destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl)|].
      destruct (D a NE) as [HY Hd]. split; [exact (conj HY NR)|].
      destruct (decide (M' a = M a)) as [E2 | NE2]; [rewrite E2; exact Hd | exact (proj2 (STEPM a NE2))].
  Qed.

  (* [comment removed for export] *)
  Lemma rep_cells_lt_ceil : forall st Lc FF a, WF bt st Lc FF -> rep_cells bt st Lc FF a -> a < CEIL.
  Proof using BT_ia.
    intros st Lc FF a W RCa. pose proof ceil_rng as CR. pose proof (img_lits bt st Lc FF W) as [I1 I2].
    destruct (rep_cells_zone bt st Lc FF W a RCa) as [K | [K | K]].
    - destruct K as [K _]. rewrite BT_ia in K. cbn [ia_img_lo ia_img_hi asan_addrs] in K. lia.
    - exact (proj1 (proj2 (dyn_kind_facts bt st Lc FF W a K))).
    - destruct K as [K _]. unfold SB in K. assert (CEIL / 8 <= CEIL / 2) by (apply Z.div_le_compat_l; lia).
      assert (2 * (CEIL / 2) <= CEIL) by (apply Z.mul_div_le; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma repx_frame_step : forall (Y : Z -> Prop) st Lc FF (M M' : mem) mdl mdl',
    WF bt st Lc FF -> RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> ~ rep_cells bt st Lc FF (U a) /\ M' a <> None) ->
    MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' ->
    RepX bt Y st Lc FF M' mdl'.
  Proof using.
    intros Y st Lc FF M M' mdl mdl' W RX CH MI SBM.
    apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => Y z /\ ~ False) Y); [intros z [Hz _]; exact Hz|].
    apply (repx_step Y (fun _ => False) (fun z => ~ rep_cells bt st Lc FF z) Xdec_false st st Lc Lc FF FF M M' mdl mdl' RX CH ltac:(intros a F; destruct F)).
    intros N0 N0' RPn Dn DIFF _ _.
    apply (Rep_sbm bt st Lc FF N0' mdl mdl'); [| exact MI | exact SBM].
    apply (Rep_frame bt st Lc FF N0 N0' mdl W RPn). intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. exact (conj F Dd).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem popC_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> a_cinit st = true ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128)
                      /\ ~ (fa_beg SBEG c <= z < fa_beg SBEG c + r_mapped_fa (a_reg st c))) ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in let newn := carve_n r c in
    r_alloc_user r + csize c <= r_mapped_user r -> 4 * (nf + newn) <= r_mapped_fa r -> r_alloc_user r + newn * csize c <= AMAX ->
    pf_regs sp (reginfo bt c) SBEG c regs -> getr regs 10 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 (nf + newn) ->
    getr regs 19 = Z_to_bv 64 newn -> getr regs 20 = Z_to_bv 64 (r_mapped_user r - r_alloc_user r) ->
    (CEIL + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn ASEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn ASEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_carve SBEG st c) Lc FF -> RepX bt (XL c) (op_carve SBEG st c) Lc FF M' mdl' -> same_but_materialized mdl mdl' ->
        (forall a : word, M' a <> M a ->
            ((fa_beg SBEG c + 4 * nf <= U a < fa_beg SBEG c + 4 * (nf + newn)) \/ (reginfo bt c + 16 <= U a < reginfo bt c + 128)) /\ M' a <> None) ->
        pf_post1 sp ra s0v s1v s2v s3v s4v s5v s6v regs r' ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50f68%bv : word) M rom) mdl) Qok Qf.
  Proof using BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v Qok Qf Hc W RX HALT CINIT XOFF r nf newn HAU FIT ROOMC
           HR H10 H9 H19 H20 Hsp Hret Sra Ss0 Ss1 Ss2 Ss3 Ss4 Ss5 Ss6 CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    destruct RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold nf in E7.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    pose proof (csize_pos c Hc) as [CS1 CS2].
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & Y2 & Y3 & Y4 & _). fold r in Y1a, Y1b, Y2, Y3, Y4.
    assert (ERI : reginfo bt c = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (EFA : fa_beg SBEG c = SBEG + c * 2 ^ 32 + 0xE0000000) by ((lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (N0 : 0 <= newn) by ((lazymatch goal with |- ?G => let G' := eval unfold newn, carve_n in G in change_no_check G' end); apply Z.div_pos; lia).
    assert (ENEW : (r_mapped_user r - r_alloc_user r) / csize c = newn) by reflexivity.
    unfold KSPACE, PG, KUSERMAP, KREGION_EXHAUST in *.
    set (RIz := reginfo bt c) in *. set (FAB := fa_beg SBEG c) in *.
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz FAB nf in G0, G8, G16, G24, G32, G40, G48, G56, G68, GW, F1, F2, F3.
    rewrite BT_segs in *.
    destruct R14 as (Bw1 & Bw2 & _).
    (* [comment removed for export] *)
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XFA : forall i, FAB <= i < FAB + r_mapped_fa r -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj2 (XOFF i Hx) Hi) | fold RIz in Hl; lia]. }
    assert (RDRI : forall k v, 8 <= k -> k + 8 <= 128 -> rdn ASEGS M0 (Z_to_bv 64 (RIz + k)) 8 = Some v -> rdn ASEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. apply (repx_rd (XL c) M M0 D (RIz + k) 8 v); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact Hr]. }
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
    assert (WFA : writableZ ASEGS M FAB (FAB + r_mapped_fa r)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact F2]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHfa : forall z, FAB <= z < FAB + r_mapped_fa r -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c); [exact Hc | exact Hz]. }
    assert (HOFF : forall lo n, 0 <= lo -> lo + n < 2 ^ 64 -> (forall z, lo <= z < lo + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n).
    { intros lo n L0 L1 Hz x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    apply (pf_carve_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v s6v
             RIz SBEG c (r_alloc_user r) (r_mapped_user r) nf Qok Qf HR H10 H9 H19 H20 ltac:(lia) Hret Hc ltac:(lia) ltac:(rewrite ENEW; lia) ltac:(lia) ltac:(lia)
             (RDRI 32 _ ltac:(lia) ltac:(lia) G32) (RDRI 16 _ ltac:(lia) ltac:(lia) G16) (RDRI 48 _ ltac:(lia) ltac:(lia) G48)
             (RDRI 40 _ ltac:(lia) ltac:(lia) G40) (RDRI 56 _ ltac:(lia) ltac:(lia) G56)).
    - apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - fold FAB newn. apply (writableZ_sok M FAB (FAB + r_mapped_fa r)); [exact WFA | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; rewrite Z2Nat.id by lia; lia | lia].
    - exact Sra. - exact Ss0. - exact Ss1. - exact Ss2. - exact Ss3. - exact Ss4. - exact Ss5. - exact Ss6.
    - apply HOFF; [lia | lia | exact NHri].
    - fold FAB newn. apply HOFF; [lia | lia | intros z Hz; apply NHfa; lia].
    - apply HOFF; [lia | lia | intros z Hz; apply NHs; lia].
    - exact HALT.
    - apply lazy_cover_HID.
    - exact Bw1.
    - exact Bw2.
    - intros r' mdlm SBM MIm POST. fold FAB newn.
      set (top := SBEG + c * 2 ^ 32 + 3758096384 + 4 * (nf + newn)).
      assert (ETOP : top = FAB + 4 * (nf + newn)) by ((lazymatch goal with |- ?G => let G' := eval unfold top in G in change_no_check G' end); rewrite EFA; lia).
      set (M' := pf_mc M RIz top (r_alloc_user r) (csize c) nf newn).
      assert (OUT : forall x : word, (U x < FAB + 4 * nf \/ FAB + 4 * (nf + newn) <= U x) -> (U x < RIz \/ RIz + 128 <= U x) -> M' x = M x).
      { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply pf_mc_outside; [exact N0 | lia | lia | lia | lia | lia | exact X2]. }
      assert (UNCH : forall a : word, (RIz <= U a < RIz + 16 \/ RIz + 24 <= U a < RIz + 32 \/ RIz + 40 <= U a < RIz + 68 \/ RIz + 69 <= U a < RIz + 128) -> M' a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M', pf_mc in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | first [rewrite length_N_to_le_bytes | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end)]; rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                                   | first [rewrite length_N_to_le_bytes | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end)]; rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ha; lia]).
        apply pf_cv_outside; rewrite ?Z2Nat.id by lia; [lia | lia | clear - Ha ETOP E5 E6 E9 N0 FIT; lia]. }
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((FAB + 4 * nf <= U a < FAB + 4 * (nf + newn)) \/ (RIz + 16 <= U a < RIz + 24) \/ (RIz + 32 <= U a < RIz + 40) \/ U a = RIz + 68) /\ M' a <> None).
      { intros a Ha.
        assert (IN : (FAB + 4 * nf <= U a < FAB + 4 * (nf + newn)) \/ (RIz <= U a < RIz + 128)).
        { destruct (Z_lt_le_dec (U a) (FAB + 4 * nf)) as [C1|C1]; [exfalso; apply Ha; apply OUT; lia|].
          destruct (Z_lt_le_dec (U a) (FAB + 4 * (nf + newn))) as [C2|C2]; [left; lia|].
          destruct (Z_lt_le_dec (U a) RIz) as [C3|C3]; [exfalso; apply Ha; apply OUT; lia|].
          destruct (Z_lt_le_dec (U a) (RIz + 128)) as [C4|C4]; [right; lia | exfalso; apply Ha; apply OUT; lia]. }
        assert (DEF : M a <> None).
        { destruct IN as [I1 | I2]; [destruct (WFA (U a) ltac:(lia)) as [Dd _] | destruct (WRI (U a) ltac:(lia)) as [Dd _]];
            rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
        split; [| exact (pf_mc_grows M RIz top (r_alloc_user r) (csize c) nf newn a DEF)].
        destruct IN as [I1 | I2]; [left; exact I1|]. right.
        destruct (Z_lt_le_dec (U a) (RIz + 16)) as [C5|C5]; [exfalso; apply Ha, UNCH; lia|].
        destruct (Z_lt_le_dec (U a) (RIz + 24)) as [C6|C6]; [left; lia|].
        destruct (Z_lt_le_dec (U a) (RIz + 32)) as [C7|C7]; [exfalso; apply Ha, UNCH; lia|].
        destruct (Z_lt_le_dec (U a) (RIz + 40)) as [C8|C8]; [right; left; lia|].
        destruct (Z_lt_le_dec (U a) (RIz + 68)) as [C9|C9]; [exfalso; apply Ha, UNCH; lia|].
        destruct (Z_lt_le_dec (U a) (RIz + 69)) as [C10|C10]; [right; right; lia | exfalso; apply Ha, UNCH; lia]. }
      assert (W' : WF bt (op_carve SBEG st c) Lc FF) by (apply (OPS_WF_carve_pf bt st Lc FF c W Hc CINIT); fold r nf newn; [exact ROOMC | exact FIT]).
      assert (RX' : RepX bt (XL c) (op_carve SBEG st c) Lc FF M' mdlm).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step (XL c) (fun _ => False)
                 (fun z => (FAB + 4 * nf <= z < FAB + 4 * (nf + newn)) \/ (RIz + 16 <= z < RIz + 24) \/ (RIz + 32 <= z < RIz + 40) \/ z = RIz + 68)
                 Xdec_false st (op_carve SBEG st c) Lc Lc FF FF M M' mdl mdlm (ex_intro _ M0 (conj RP D)) FOOTM ltac:(intros a F; destruct F)).
        intros N0m N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, (FAB + 4 * nf <= U a < FAB + 4 * (nf + newn)) \/ (RIz + 16 <= U a < RIz + 128) -> N0' a = M' a).
        { intros a Ha. apply SAME. apply (repx_off (XL c) M N0m Dn). destruct Ha as [Ha | Ha]; [apply XFA; lia | apply XRI; lia]. }
        assert (RDN : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
                   ((FAB + 4 * nf <= z /\ z + Z.of_nat k <= FAB + 4 * (nf + newn)) \/ (RIz + 16 <= z /\ z + Z.of_nat k <= RIz + 128)) ->
                   rdn ASEGS M' (Z_to_bv 64 z) k = Some v -> rdn ASEGS N0' (Z_to_bv 64 z) k = Some v).
        { intros z k v Z0 Z1 IN Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
          apply EQF. clear - Hx IN. lia. }
        destruct (pf_mc_rd ASEGS M RIz top (r_alloc_user r) (csize c) nf newn N0 ltac:(lia) ltac:(lia) ltac:(lia)) as (P16 & P32 & P68 & PENT).
        apply (OPS_REP_carve_pf bt st Lc FF N0m N0' mdl mdlm c W RPn Hc); fold r nf newn RIz FAB; rewrite ?BT_segs.
        - exact FIT.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_carve in G in change_no_check G' end). fold r nf newn RIz FAB.
          destruct F as [F | [F | [F | F]]]; [left; exact F | right; left; exact F | right; right; left; exact F | right; right; right; left; exact F].
        - intros i k Hnth. unfold carve_list in Hnth. rewrite nth_error_map in Hnth.
          destruct (nth_error (seq 0 (Z.to_nat newn)) i) as [i0|] eqn:Es; [|discriminate Hnth]. cbn [option_map] in Hnth. injection Hnth as <-.
          assert (Hi : (i < Z.to_nat newn)%nat) by (rewrite <- (length_seq (Z.to_nat newn) 0); apply nth_error_Some; rewrite Es; discriminate).
          assert (Ei0 : i0 = i) by (pose proof (nth_error_nth _ _ 0%nat Es) as En; rewrite seq_nth in En by exact Hi; lia). subst i0.
          (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
          set (j := newn - 1 - Z.of_nat i).
          pose proof (PENT (Z.to_nat j) ltac:((lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia)) as PE. rewrite Z2Nat.id in PE by ((lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia).
          replace (top - 4 * (j + 1)) with (FAB + 4 * (nf + Z.of_nat i)) in PE by ((lazymatch goal with |- ?G => let G' := eval unfold j in G in change_no_check G' end); lia).
          apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
          replace (compact_of SBEG c (chunk_addr SBEG c (r_alloc_user r / csize c + j))) with ((r_alloc_user r + j * csize c) / 16); [exact PE|].
          (lazymatch goal with |- ?G => let G' := eval unfold compact_of, chunk_addr in G in change_no_check G' end). f_equal.
          assert (EAU : r_alloc_user r = csize c * (r_alloc_user r / csize c)) by (apply Z.div_exact; [lia | exact Y4]).
          set (j0 := r_alloc_user r / csize c) in *. rewrite EAU at 1. ring.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P16].
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P32].
        - (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite w2b1 by lia. apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact P68].
        - exact SBM.
        - exact MIm. }
      apply (CONT r' M' mdlm W' RX' SBM); [| exact POST].
      intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [|exact Dd]. fold FAB RIz. clear - F. lia.
  Qed.
End L3.
End WithCeil.
End AsAllocM8La.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMHyp.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition malloc_cells (bt : as_boot) (TP TSDP PGP FL MIDEND : Z) : Prop :=
  In (0x10827c, 4%nat, 30) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0xff260, 8%nat, 0x1990a8) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x1990ca, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x108258, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0xff250, 8%nat, PGP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (PGP, 8%nat, 4096) (bt_consts bt)
  /\ In (0x106de0, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x106de4, 4%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (TP - 88, 8%nat, TSDP) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (TSDP, 8%nat, bt_tctx bt) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x1897e2, 1%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x10490, 8%nat, 0x0218a392cd3d5dbf) (bt_consts bt)    (* [comment removed for export] *)
  /\ In (0x10504, 1%nat, 3) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (0x10608, 1%nat, 4) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (0x10631, 1%nat, 11) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x104d40, 2%nat, 16) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (0x104d42, 2%nat, 2048) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (0x104d38, 8%nat, 2 ^ 40) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x103f38, 8%nat, bt_spacebeg bt) (bt_consts bt)       (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ In (0x106ddc, 1%nat, 1) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0xff270, 8%nat, 0x107578) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0xff278, 8%nat, 0x108268) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108268, 8%nat, 0) (bt_consts bt)
  /\ In (0xff280, 8%nat, 0x108270) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108270, 8%nat, MIDEND) (bt_consts bt)
  /\ In (0xff288, 8%nat, 0x108260) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x108260, 8%nat, 0x7fffffffffff) (bt_consts bt)
  /\ In (0xff268, 8%nat, FL) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (FL + 85, 1%nat, 1) (bt_consts bt)                     (* [comment removed for export] *)
  /\ In (FL + 44, 4%nat, 4096) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (FL + 52, 4%nat, 0xbe) (bt_consts bt)                  (* [comment removed for export] *)
  /\ In (0xff290, 8%nat, 0x1011b0) (bt_consts bt)             (* [comment removed for export] *)
  /\ In (0x1011b0, 8%nat, 0xf56e4) (bt_consts bt)
  /\ In (0xffec8, 8%nat, 0x10) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (TP + 0x10, 4%nat, 0) (bt_consts bt)                   (* [comment removed for export] *)
  /\ In (0x103b8, 8%nat, MAGIC) (bt_consts bt)                 (* [comment removed for export] *)
  /\ In (0x199040, 8%nat, 0) (bt_consts bt)                    (* [comment removed for export] *)
  /\ In (0x1990a8 + 120, 8%nat, 18446744073709551615) (bt_consts bt)          (* [comment removed for export] *)
  (* [comment removed for export] *)
  /\ (0x10000 <= TSDP /\ TSDP + 8 <= 0x65d000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x65d000 /\ 0x10000 <= FL /\ FL + 4096 < 0x65d000
      /\ 0 <= MIDEND < 2 ^ 64 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x65d000).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Xm (S T c p : Z) (z : Z) : Prop :=
  (S - 2480 <= z < S)
  \/ (T + T_PC + PC_SZ * c <= z < T + T_PC + PC_SZ * c + 4)
  \/ (T + 2784 <= z < T + 2792)
  \/ (p - 15 <= z < p - 8).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CHUNK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model).
  Variables (n : Z) (ks : list Z) (k : Z).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M mdl.
  Hypothesis Hn : 1 <= n <= 64512.
  #[local] Abbreviation c := (class_of (needed n)).
  Hypothesis HC : a_cache st c = ks ++ [k].
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation ab := (chunk_of_compact (bt_spacebeg bt) (class_of (needed n)) k).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SG := (bt_segs bt).

  Lemma mc_needed : 24 <= needed n <= 65536 /\ needed n mod 8 = 0 /\ 1 <= c <= 30 /\ needed n <= csize c /\ is_primary n = true
                    /\ needed n = rounded n + rz n /\ Z.max n 8 <= rounded n <= Z.max n 8 + 7 /\ 16 <= rz n <= 1024.
  Proof using Hn.
    pose proof (rz_log_range n) as RL. pose proof (needed_facts n Hn) as [NB N8].
    assert (Hrz : 16 <= rz n <= 1024).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    assert (Hnd : needed n = rounded n + rz n) by reflexivity.
    assert (Hrd : Z.max n 8 <= rounded n <= Z.max n 8 + 7).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    split; [exact NB|]. split; [exact N8|]. split; [apply class_of_range; lia|]. split; [apply csize_class_of; lia|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold is_primary in G in change_no_check G' end); apply Z.leb_le; lia|]. split; [exact Hnd|]. split; [exact Hrd | exact Hrz].
  Qed.

  Lemma mc_in : In k (a_cache st c).
  Proof using HC ks. rewrite HC. apply in_app_iff. right. left. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma mc_chunk :
    carved bt st c ab /\ AS_HEAPLO <= ab /\ ab + csize c <= CEIL /\ ab mod 16 = 0 /\ 0 <= k < 2 ^ 32
    /\ (ab + csize c <= T \/ T + PG <= ab)
    /\ (bt_tctx bt + 0x10000 <= ab \/ ab + csize c <= bt_tctx bt)
    /\ (forall p m, In (p, m) Lc -> ab + csize c <= p - 16 \/ p + up8 m <= ab)
    /\ (forall b, In b (a_tq st ++ a_gq st) -> ab + csize c <= ba_addr b \/ ba_addr b + BATCHSZ <= ab)
    /\ (forall z, ab <= z < ab + csize c -> lzb mdl z = false)
    /\ writableZ SG M ab (ab + csize c)
    /\ (forall z, ab <= z < ab + csize c -> rt_priv (bt_ia bt) Lc FF z).
  Proof using HC Hn RP W ks. pose proof mc_needed as (_ & _ & Hc & _). exact (OBL_cache_chunk_pf bt st Lc FF M mdl c k W RP Hc mc_in). Qed.

  (* [comment removed for export] *)
  Lemma mc_pclass :
    cellZ SG M (T + T_PC + PC_SZ * c) 4 (Z.of_nat (length ks) + 1)
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 16 + 4 * Z.of_nat (length ks)) 4 k
    /\ (exists csz, cellZ SG M (T + T_PC + PC_SZ * c + 8) 8 csz)
    /\ Z.of_nat (length ks) + 1 <= 16.
  Proof using HC Hn RP W mdl FF Lc st RC.
    pose proof mc_needed as (_ & _ & Hc & _).
    destruct RP as (_ & _ & RT & _). destruct RT as (_ & _ & _ & _ & _ & _ & _ & PC & _).
    destruct (PC c Hc) as (X1 & X2 & X3 & X4). rewrite HC in X1, X4. rewrite length_app in X1. cbn [length] in X1.
    replace (Z.of_nat (length ks + 1)) with (Z.of_nat (length ks) + 1) in X1 by lia.
    split; [exact X1|]. split.
    - apply X4. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
    - split; [wd_eexists; exact X3|].
      destruct W as (_ & WC & _). destruct (WC c Hc) as (L & _). rewrite HC, length_app in L. cbn [length] in L.
      assert (CM : cache_max c <= 16) by ((lazymatch goal with |- ?G => let G' := eval unfold cache_max, cache_hint in G in change_no_check G' end); lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_vs_node : forall id z, 1 <= id <= dp_nids (a_dep st) -> ab <= z < ab + csize c -> ~ foot_node bt (a_dep st) id z.
  Proof using HC Hn RP W ks mdl M FF Lc RC.
    intros id z Hid Hz HN. pose proof mc_needed as (_ & _ & Hc & _). pose proof mc_chunk as (CV & _).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (_ & _ & S1 & S2 & _).
    unfold foot_node in HN.
    destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
    set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
    destruct HIn as [Eb | Hnb].
    - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & INN & _) & _).
      rewrite Eb in INN. destruct (space_vs_fixed bt st Lc FF W _ _ INN ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)); unfold PG in *; lia.
    - destruct (space_vs_dyn bt st Lc FF W _ _ (node_dyn st bb Hnb)); unfold PG in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_T_stack_vs_node : forall id z, 1 <= id <= dp_nids (a_dep st) -> (T <= z < T + PG \/ CEIL <= z) -> ~ foot_node bt (a_dep st) id z.
  Proof using W FF Lc.
    intros id z Hid Hz HN. unfold foot_node in HN.
    destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
    set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
    destruct (node_blocks_range bt st Lc FF W bb HIn) as (B1 & B2 & B3).
    destruct Hz as [Hz | Hz]; [| unfold CEIL, PG in *; lia].
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & PW & _ & _ & _ & _ & INFS & INT & INN & _) & _).
    destruct HIn as [Eb | Hnb].
    - pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ INN)
                    ltac:(intros EQ; injection EQ; intros; unfold PG in *; lia)) as D. hnf in D. cbn in D. rewrite <- Eb in *. unfold PG in *. lia.
    - pose proof (ar_disj_fixed_dyn bt st Lc FF _ _ W INT (node_dyn st bb Hnb)) as D. hnf in D. cbn in D. unfold PG in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_shadow_ab : exists b, byteZ SG M (SB + ab / 8) b /\ (b = FD \/ b = FA).
  Proof using HC Hn RP W ks mdl FF Lc st RC.
    pose proof mc_needed as (_ & _ & Hc & _). pose proof mc_chunk as (CV & A1 & A2 & A16 & _ & _ & _ & LIV & _).
    destruct (carved_range bt st Lc FF W c ab Hc CV) as (R1 & R2 & S1 & S2 & _).
    destruct W as ((WR & _) & _). destruct (WR c Hc) as (Q1 & _). 
    destruct RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS & _). destruct RS as (SH1 & _).
    pose proof (csize_pos c Hc) as ((C1 & C2) & C3).
    assert (G : region_beg SBEG c / 8 <= ab / 8 < (region_beg SBEG c + r_mapped_user (a_reg st c)) / 8).
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). split; [apply Z.div_le_mono; lia | lia]. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NL : ~ live_granule Lc (ab / 8)).
    { intros (p & m & Hin & G1 & G2). destruct (LIV p m Hin) as [D|D].
      - pose proof (live_range bt st Lc FF W p m Hin) as (_ & _ & Lm & Lp).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). unfold up8 in D. lia.
      - pose proof (live_range bt st Lc FF W p m Hin) as (_ & _ & Lm & Lp). pose proof (up8_facts m ltac:(lia)) as (U1 & U2 & U3 & U4).
        unfold up8 in *. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exists (if existsb (fun mn : Z * Z => ((fst mn + 16) / 8 <=? ab / 8) && (ab / 8 <? (fst mn + 16 + snd mn + 7) / 8))%bool (quar st) then FD else FA).
    split; [exact (SH1 c (ab / 8) Hc G NL)|]. destruct (existsb _ _); [left | right]; reflexivity.
  Qed.
End CHUNK.
End AsAllocMHyp.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Lk.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsanPlanSoundSums AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w AsAllocM8La.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Definition pop_cells (bt : as_boot) : Prop :=
  In (0x103f40, 4%nat, 0xffffffff) (bt_consts bt)               (* [comment removed for export] *)
  /\ In (0x103f48, 8%nat, bt_spacebeg bt + KSPACE) (bt_consts bt) (* [comment removed for export] *)
  /\ In (0x103f50, 1%nat, 0) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0x1991ac, 1%nat, 0) (bt_consts bt)                      (* [comment removed for export] *)
  /\ In (0x199138, 8%nat, 0) (bt_consts bt).                     (* [comment removed for export] *)

Section POPKIT.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  Variables (Y : Z -> Prop) (st : ast) (Lc FF : list (Z * Z)) (M M0 : mem) (mdl : Model).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M0 mdl.
  Hypothesis D : forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None.
  Hypothesis YIMG : forall z, Y z -> ~ (AIMGLO <= z < AIMGHI).
  Hypothesis YCTX : forall z, Y z -> ~ (CTX + 152 <= z < CTX + 160).

  Lemma pk_def : forall a : word, M0 a <> None -> M a <> None.
  Proof using D Y.
    intros a H0. destruct (decide (M a = M0 a)) as [E | NE]; [rewrite E; exact H0 | exact (proj2 (D a NE))].
  Qed.

  Lemma pk_const : forall a (n : nat) v, In (a, n, v) (bt_consts bt) -> AIMGLO <= a -> a + Z.of_nat n <= AIMGHI ->
    rdn ASEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
  Proof using YIMG D RP mdl M0 FF Lc st Y BT_segs RC.
    intros a n v Hin A0 A1. pose proof RP as (R1 & _). rewrite BT_segs in R1.
    apply (repx_rd Y M M0 D a n); [lia | lia | intros i Hi; intros HY; exact (YIMG i HY ltac:(lia)) | exact (const_cell bt M0 _ _ _ R1 Hin)].
  Qed.

  Lemma pk_shadow_def : forall z, shmaps z -> M (Z_to_bv 64 z) <> None.
  Proof using D RP mdl M0 FF Lc st Y bt RC.
    intros z Hz. apply pk_def. pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15).
    destruct R15 as (_ & _ & _ & _ & SHD). first [exact (SHD z Hz) | exact (proj1 SHD z Hz)].   (* [comment removed for export] *)
  Qed.

  Lemma pk_thread_geom : 0 < T /\ T + 4096 <= CEIL /\ 0 < CTX /\ CTX + 0x10000 <= CEIL /\ T mod 4096 = 0
    /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T) /\ (CTX + 0x10000 <= AIMGLO \/ AIMGHI <= CTX).
  Proof using W FF Lc st BT_ia.
    pose proof (fixed_facts bt st Lc FF W) as (T1 & T2 & C1 & C2 & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    rewrite BT_ia in D4, E4. cbn [ia_img_lo ia_img_hi asan_addrs] in D4, E4. unfold PG in *.
    repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_T_writable : writableZ ASEGS M T (T + 4096).
  Proof using D RP W mdl M0 FF Lc st Y BT_ia BT_segs RC.
    pose proof pk_thread_geom as (T1 & T2 & _). pose proof ceil_rng as CR.
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _). rewrite BT_segs in TW. unfold PG in TW.
    apply (repx_wr Y M M0 D); [lia | lia | exact TW].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_junk8 : forall lo hi z, writableZ ASEGS M lo hi -> lo <= z -> z + 8 <= hi -> 0 <= z -> hi < 2 ^ 64 ->
    exists v : word, rdn ASEGS M (Z_to_bv 64 z) 8 = Some (LE8 v).
  Proof using.
    intros lo hi z WR L H Z0 H1.
    destruct (rdn_defined_ex ASEGS M (Z_to_bv 64 z) 8) as (bs & Cbs & Lbs).
    { intros i Hi. rewrite u_Z2bv in Hi by lia. cbn in Hi. exact (proj1 (WR i ltac:(lia))). }
    { rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Cbs. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lbs | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma pk_poisonH : forall (slot : Z) (ra fsp : word),
    AS_HEAPLO <= slot -> slot + 2 ^ 18 <= CEIL -> slot mod 8 = 0 ->
    CEIL + 64 <= U fsp -> U fsp + 16 <= 2 ^ 47 -> writableZ ASEGS M (U fsp - 64) (U fsp) -> ret_ok ra ->
    poisonH ASEGS asan_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0.
  Proof using YIMG D RP mdl M0 FF Lc st Y CELLS FL PGP TSDP TP BT_ia BT_segs bt.
    intros slot ra fsp S0 S1 S8 F0 F1 WST Hret. pose proof ceil_rng as CR. pose proof (u64_range fsp) as Hf.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    assert (CSB : rdn ASEGS M (Z_to_bv 64 0x107578) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000))).
    { pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R15). destruct R15 as (_ & _ & Csb & _).
      rewrite BT_ia, BT_segs in Csb. cbn [ia_rtc_sb asan_addrs] in Csb. unfold SB in Csb.
      apply (repx_rd Y M M0 D 0x107578 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; exact (YIMG i HY ltac:(cbn in Hi; lia)) | exact Csb]. }
    unfold AS_HEAPLO in S0.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
    - exact (pk_const _ _ _ CELL_gsh ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact CSB.
    - exact (pk_const _ _ _ CELL_gmb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_mb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_gme ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_me ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_ghe ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_he ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_grm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (word_to_le_bytes 8 (1005284 : word)) with (LE8 (Z_to_bv 64 0xf56e4)) by reflexivity.
      exact (pk_const _ _ _ CELL_rm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - vm_compute. discriminate.
    - apply ret_ok_even. reflexivity.
    - intros _. split; [| vm_compute; discriminate]. rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_cpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact S8.
    - rewrite u_Z2bv by lia. reflexivity.
    - left. rewrite !u_Z2bv by lia. lia.
    - lia.
    - apply (writableZ_sok M (U fsp - 64) (U fsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia.
      assert (Q : 0x10007fff8000 / 8 <= slot / 8 /\ slot / 8 + 2 ^ 15 <= CEIL / 8).
      { split; [apply Z.div_le_mono; lia|]. replace (slot / 8 + 2 ^ 15) with ((slot + 2 ^ 18) / 8) by (rewrite <- (Z.div_add slot (2 ^ 15) 8) by lia; f_equal).
        apply Z.div_le_mono; lia. }
      assert (Q2 : CEIL / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
      assert (E1 : 0x10007fff8000 / 8 = 2199291686912) by reflexivity. assert (E2 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity.
      rewrite E1 in Q. rewrite E2 in Q2.
      apply store_ok_of_all; [rewrite u_Z2bv by lia; change (2 ^ 18 / 8) with (2 ^ 15); rewrite Z2Nat.id by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. change (2 ^ 18 / 8) with (2 ^ 15) in Hx. rewrite Z2Nat.id in Hx by lia.
      assert (DEF : M x <> None).
      { rewrite <- (Z_to_bv_bv_unsigned _ x). apply pk_shadow_def. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO, AS_LO, AS_GAPLO in G in change_no_check G' end). right. lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (M x); [discriminate | exfalso; exact (DEF eq_refl)].
    - exact Hret.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_gctH : forall (gsp tp : word), U tp = TP -> CEIL + 16 <= U gsp -> U gsp + 8 <= 2 ^ 47 -> writableZ ASEGS M (U gsp - 8) (U gsp) ->
    gctH ASEGS asan_gct_tab M gsp tp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) (Z_to_bv 64 T).
  Proof using YCTX YIMG D RP W mdl M0 FF Lc st Y CELLS MIDEND FL PGP BT_ia BT_segs.
    intros gsp tp Etp G0 G1 WST. pose proof ceil_rng as CR. pose proof (u64_range gsp) as Hg. pose proof (u64_range tp) as Htp.
    pose proof pk_thread_geom as (T1 & T2 & C1 & C2 & _).
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x65d000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x65d000).
    { do 28 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & _ & _ & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gc1 & Gc2 & Gc8 & Gc9).
    pose proof RP as (_ & _ & R3 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Tback & _). rewrite BT_segs in Tback.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
    - rewrite <- (w2b1 1) by lia. exact (pk_const _ _ _ CELL_kif ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 0x106de0) 4) with (Z_to_bv 64 0x106de4 : word) by (apply bv_eq; reflexivity).
      exact (pk_const _ _ _ CELL_key ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia).
      exact (pk_const _ _ _ CELL_tsdp ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const _ _ _ CELL_tctx ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite (u_Z2bv CTX) by lia; reflexivity).
      apply (repx_rd Y M M0 D (CTX + 152) 8); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; intros HY; exact (YCTX i HY ltac:(cbn in Hi; lia)) | exact Tback].
    - rewrite u_Z2bv by lia. lia.
    - apply (writableZ_sok M (U gsp - 8) (U gsp)); [exact WST | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - lia.
    - rewrite u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_thread_geom2 :
    (T + 4096 <= AS_LO \/ AS_HEAPLO <= T) /\ (CTX + 0x10000 <= AS_LO \/ AS_HEAPLO <= CTX)
    /\ (T + 4096 <= SBEG \/ SBEG + KSPACE + 4096 <= T) /\ (CTX + 0x10000 <= SBEG \/ SBEG + KSPACE + 4096 <= CTX)
    /\ 0 < SBEG /\ SBEG + KSPACE + 4096 <= CEIL /\ AS_HEAPLO <= SBEG.
  Proof using W FF Lc st.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & _ & _ & _ & _ & _ & _ & INT & _ & _ & INC & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INT)) as ((D1 & D2 & D3 & D4 & D5) & _ & D6 & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ INC)) as ((E1 & E2 & E3 & E4 & E5) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as TS.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as CS.
    unfold PG in *. repeat split; try assumption; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pk_nolazy_rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> lzb mdl z = false.
  Proof using RP W M0 FF Lc st RC.
    intros z Hz. pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    apply (OBL_nolazy_rt st Lc FF M0 mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). tauto.
  Qed.
End POPKIT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MKH.
  Variable bt : as_boot.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.

  Lemma mkH_notlazy : forall (mdl : Model) (A : list (Z * Z)) z, 0 <= z < 2 ^ 64 -> lzb mdl z = false -> mkH (m_vm_lazy mdl) A (Z_to_bv 64 z) = false.
  Proof using. intros mdl A z Hz L. (lazymatch goal with |- ?G => let G' := eval unfold mkH in G in change_no_check G' end). unfold lzb in L. rewrite L. reflexivity. Qed.
  Lemma mkH_allowed : forall (L : list (word * word)) (A : list (Z * Z)) z, page_allowedb A (page_base (Z_to_bv 64 z)) = true -> mkH L A (Z_to_bv 64 z) = false.
  Proof using. intros L A z Ha. (lazymatch goal with |- ?G => let G' := eval unfold mkH in G in change_no_check G' end). rewrite Ha. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply andb_false_r. Qed.
  Lemma mkH_off_zone : forall st (mdl : Model) (A : list (Z * Z)) z, rep_ledger bt st mdl -> 0 <= z < 2 ^ 64 ->
    (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> mkH (m_vm_lazy mdl) A (Z_to_bv 64 z) = false.
  Proof using BT_ia.
    intros st mdl A z RL Hz Hr. apply mkH_notlazy; [exact Hz|]. destruct (lzb mdl z) eqn:E; [|reflexivity].
    exfalso. pose proof (lazy_zone bt st mdl z RL Hz E) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2. lia.
  Qed.
  Lemma mkH_off_segments : forall st (mdl : Model) (A : list (Z * Z)), rep_ledger bt st mdl -> H_off_segments ASEGS (mkH (m_vm_lazy mdl) A).
  Proof using BT_ia.
    intros st mdl A RL a Ha. unfold mkH in Ha. apply andb_prop in Ha as [Ha _]. pose proof (u64_range a).
    assert (L : lzb mdl (U a) = true) by ((lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Z_to_bv_bv_unsigned; exact Ha).
    destruct (lazy_zone bt st mdl (U a) RL ltac:(lia) L) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi asan_addrs] in Z2.
    destruct (find_segment ASEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate.
  Qed.
  (* [comment removed for export] *)
  Lemma lazy_cover_sub : forall (Hd : word -> bool) (lazy lazy' : list (word * word)) (A : list (Z * Z)),
    lazy_cover Hd lazy A -> (forall p, page_in_ranges p lazy' = true -> page_in_ranges p lazy = true) -> lazy_cover Hd lazy' A.
  Proof using. intros Hd lazy lazy' A LC SUB w Hl Hw. exact (LC w (SUB _ Hl) Hw). Qed.
End MKH.

(* [comment removed for export] *)
Lemma sh_band : forall p n, AS_HEAPLO <= p -> 0 <= n -> p + n <= CEIL -> n mod 8 = 0 ->
  AS_GAPHI <= SB + p / 8 /\ SB + p / 8 + n / 8 <= AS_HEAPLO /\ SB + p / 8 + n / 8 < CEIL.
Proof using.
  intros p n P0 N0 P1 N8. pose proof ceil_rng as CR. unfold AS_HEAPLO, AS_GAPHI, SB in *.
  assert (Q1 : 0x10007fff8000 / 8 <= p / 8) by (apply Z.div_le_mono; lia).
  assert (Q2 : (p + n) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (Q3 : (p + n) / 8 = p / 8 + n / 8).
  { rewrite (Z.div_mod n 8) at 1 by lia. rewrite N8, Z.add_0_r. rewrite (Z.mul_comm 8), Z.div_add by lia. reflexivity. }
  assert (E1 : 0x10007fff8000 / 8 = 2199291686912) by reflexivity. assert (E2 : 0x7fffff800000 / 8 = 17592184995840) by reflexivity.
  rewrite E1 in Q1. rewrite E2 in Q2. lia.
Qed.
End WithCeil.
End AsAllocM8Lk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8pa.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.


Lemma asan_poison_cells_img : Forall (fun c => 0 <= c /\ c + 8 <= AIMGHI) (poison_cells asan_poison_tab).
Proof. (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, asan_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). repeat constructor; lia. Qed.

Section FPGen.
Context {fx : FPState}.

Section PFARM.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments ASEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v s6v thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte)
            (RIz SPB c req au mu nf PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP MDS : Model -> Model).
  #[local] Abbreviation stats := (at_ thr 2768).
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu).
  #[local] Abbreviation SH := ((SPB + c * 2 ^ 32 + mu) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-64)) (Z_to_bv 64 0x50ef4) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                     (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x17990) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (pf_mr mem sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c mu PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f18.
  Hypothesis H11 : getr regs 11 = stats.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 RIz.
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 req.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hc : 1 <= c <= 30.
  Hypothesis Hreq : 1 <= req /\ csize c * req <= 2 ^ 18.
  Hypothesis Hau : 0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000.
  Hypothesis Hmap : mu < au + csize c * req.
  Hypothesis HSPB : 0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63 /\ SPB mod 4096 = 0 /\ AIMGHI <= SPB.
  Hypothesis Hmu4k : mu mod 4096 = 0.
  Hypothesis Hnf : 0 <= nf <= 2 ^ 27.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 464.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok ASEGS mem (at_ sp (-464)) 464 = true.
  Hypothesis C_sbeg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis R_au : rdn ASEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn ASEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis R_mm : rdn ASEGS mem (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_nf : rdn ASEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis C_rel : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 40)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff)).
  Hypothesis C_pre : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn ASEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn ASEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 464 \/ U sp <= slot.
  Hypothesis HDsbeg : hid_off Hd (0x103f18 + 32) 8.
  Hypothesis HDrel : hid_off Hd (0x103f18 + 40) 4.
  Hypothesis HDpre : hid_off Hd (0x103f18 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0xff250 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0xff260 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 464) 464.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD ASEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x80740 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD ASEGS (mkCfg (epend r1 (0x8073c : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm))
        /\ (m_halted (MDS mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MDS mdlm)) A /\ MInv A (MDS mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 464 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis HRsl : RIz + 128 <= slot \/ slot + 2 ^ 18 <= RIz.
  Hypothesis PH : poisonH ASEGS asan_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0.
  Hypothesis GH : gctH ASEGS asan_gct_tab mem (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd asan_gct_tab) + 8 <= U sp - 464 /\ U tp - 80 <= U sp - 464 /\ U tsdp + 8 <= U sp - 464 /\ U ctxw + 160 <= U sp - 464.
  Hypothesis GS : (U (gt_tsd asan_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd asan_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd asan_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd asan_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn ASEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn ASEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis Rst : rdn ASEGS mem (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis SOKT : store_ok ASEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok ASEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells asan_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd asan_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 464) 464.
  Hypothesis HDRIa : hid_off Hd RIz 128.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x50f68 ->
      getr r 10 = Z_to_bv 64 0x103f18 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
      getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) ->
      getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c) ->
      getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) -> getr r 4 = tp -> getr r 3 = gp ->
      katwD ASEGS (mkCfg (mkst r (0x4ea98 : word) (pam_3 MR sp thr v72 v80 vst RIz SPB c slot mu) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD ASEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.
  Hypothesis CONT0D : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MDS mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i pf_clob) regs r' -> pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v r' r ->
      katD ASEGS (mkCfg (mkst r ra (wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.

  Theorem pf_map_arm_katsD : katsD ASEGS (mkCfg (mkst regs (0x50dd4 : word) mem rom) model) Qok Qf.
  Proof using CONT0D CONT0K CONT1 HDRIa HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT Rst R80 R72 G4 G3 G2 G1 GS GB GH PH HRsl HTsl HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDrel HDsbeg Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre C_rel R_nf R_mm R_mu R_au C_sbeg Hstk HCF HPGP HRI Hnf Hmu4k HSPB Hmap Hau Hreq Hc Hret Hsp H22 H21 H20 H19 H18 H9 H8 H14 H13 H12 H11 H10 H3 H4 H2 H1 MDS MKP MOK thr0 T CF PGP nf mu au req c SPB RIz cpm midend vst v80 v72 ctxw tsdp gp tp thr s6v s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct HSPB as (S1 & S2 & S3 & S4).
    destruct Hau as [[AU0 AU1] AU2]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf64 : hid_off Hd (U sp - 64) 64) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf128 : hid_off Hd2 (U sp - 128) 64) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply (pf_usermap_katsD Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu PGP CF Qok Qf MOK MKP MDS
             H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq (conj (conj AU0 AU1) AU2) Hmap (conj S1 (conj S2 (conj S3 S4))) Hmu4k (conj RI1 RI2) HPGP HCF Hstk
             C_sbeg R_au R_mu R_mm C_rel C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot
             HDsbeg ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia]) ltac:(eapply hid_off_sub; [exact HDRIa | lia | lia])
             HDrel HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _ & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 464 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply pf_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply pf_mr_grows.
      assert (RDZ : forall (z : Z) (k : nat) v, 0 <= z -> z + Z.of_nat k <= U sp - 464 -> (z + Z.of_nat k <= slot \/ slot + 2 ^ 18 <= z) ->
                 rdn ASEGS mem (Z_to_bv 64 z) k = Some v -> rdn ASEGS MR (Z_to_bv 64 z) k = Some v).
      { intros z k v Z0 Z1 Z2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
        apply OUT; clear - Hx Z1 Z2; lia. }
      assert (RDT : forall (k : Z) v, 0 <= k -> k + 8 <= 4096 -> rdn ASEGS mem (at_ thr k) 8 = Some v -> rdn ASEGS MR (at_ thr k) 8 = Some v).
      { intros k v K0 K1 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        apply OUT; clear - Hx UT T2 HTsl K0 K1; lia. }
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) with MR.
      apply (pf_after_map_katwD Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp thr tp gp tsdp ctxw v72 v80 vst midend cpm RIz SPB c au mu nf T thr0 Qok Qf
               PR ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E9 E10 E19 E20 E22 (conj SP1 SP2) Hc (conj (conj AU0 AU1) AU2) Hnf ltac:(lia) ltac:(lia) ltac:(lia) HTRI HTSH HRSH).
      + apply (poisonH_keep_P ASEGS asan_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact asan_poison_cells_img]. cbv beta. intros c0 Hc0 z Hz. lia.
      + destruct GB as (B1 & B2 & B3 & B4). destruct GS as (Q1 & Q2 & Q3 & Q4).
        apply (gctH_keep_P ASEGS asan_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 464 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH);
          [intros x [X1 X2]; apply OUT; assumption | exact GR
          | intros z Hz; cbv beta; clear - Hz B1 Q1; lia | intros z Hz; cbv beta; clear - Hz B2 Q2; lia
          | intros z Hz; cbv beta; clear - Hz B3 Q3; lia | intros z Hz; cbv beta; clear - Hz B4 Q4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + apply RDT; [lia | lia | exact R72].
      + apply RDT; [lia | lia | exact R80].
      + apply RDT; [lia | lia | exact Rst].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_au].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_mu].
      + apply RDZ; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HRsl; lia | exact R_nf].
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + exact HDc.
      + exact HDf128.
      + exact HDsh.
      + exact HD1.
      + exact HD2.
      + exact HD3.
      + exact HD4.
      + exact HDT.
      + exact HDRI.
      + exact HALT4.
      + exact LC2.
      + exact AWF2.
      + exact MI2.
      + intros r mdl5 SB5 MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3.
        exact (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 D0 D1 D10 D11 D12 D13 D9 D19 D20 D4 D3).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _) & _).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (PR & E9 & E19 & E20 & E22 & E10) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & _ & (HDS & LDS & _)).
      destruct (FRAMES _ _ HDS LDS SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes (unfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-148)) SCR) (at_ sp (-148)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 64 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by (clear - SL; lia); clear - Hx Hslot; lia).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      destruct PR as (P2 & _).
      apply (pf_fail_map_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v s4v s5v s6v Qf P2 E10 Hret ltac:(lia)
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-48) s4v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-56) s5v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               (pf_slots_ext MK mem sp ra s0v s1v s2v s3v s4v s5v s6v (-64) s6v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
               HDf64 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0D r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End PFARM.
End FPGen.
End AsAllocM8pa.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8z.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section PAMRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp thr v72 v80 vst : word) (RIz SPB c slot mu : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 64.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 64.
  #[local] Abbreviation P3 := (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu).
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma pam_3_mu : rdn segs P3 (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 (mu + 2 ^ 18))).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold pam_3, pf_ms in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.


End PAMRD.

Section EAMRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp s4x s5x thr v72 v80 : word) (RIz slot mfa : Z).
  Hypothesis Hsp : 4096 <= U sp.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 64.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 64.
  #[local] Abbreviation E3 := (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).

  Lemma eam_3_mfa : rdn segs E3 (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 (mfa + 2 ^ 18))).
  Proof using HRI. (lazymatch goal with |- ?G => let G' := eval unfold eam_3, efs_ms in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. Qed.


End EAMRD.

(* [comment removed for export] *)
Lemma firstn1_skipn_repeat : forall {A} (b : A) (n i : nat), (i < n)%nat -> firstn 1 (skipn i (repeat b n)) = [b].
Proof.
  intros A b n. induction n as [|n IH]; intros i Hi; [lia|]. destruct i as [|i]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [repeat skipn] in G in change_no_check G' end). apply IH. lia.
Qed.

Lemma psfill_fill : forall segs M (fsp ra s0 s1 s2 s3 s4 s5 : word) slot (i : Z), 0 <= slot < 2 ^ 63 -> 0 <= i < 2 ^ 15 ->
  rdn segs (psfill M fsp ra s0 s1 s2 s3 s4 s5 slot) (Z_to_bv 64 (slot / 8 + 0x7fff8000 + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
Proof.
  intros segs M fsp ra s0 s1 s2 s3 s4 s5 slot i Hs Hi. destruct (psfill_shad slot Hs) as (E1 & E2 & E3).
  assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (lazymatch goal with |- ?G => let G' := eval unfold psfill in G in change_no_check G' end).
  replace (Z_to_bv 64 (slot / 8 + 0x7fff8000 + i)) with (at_ (Z_to_bv 64 (shad (Z_to_bv 64 slot))) (Z.of_nat (Z.to_nat i)))
    by (apply bv_eq; rewrite at_u by (rewrite E3, Z2Nat.id by lia; lia); rewrite E3, Z2Nat.id, u_Z2bv by lia; reflexivity).
  rewrite rdn_wbytes_sub; [ | rewrite repeat_length, E2; lia | rewrite repeat_length, E2, E3; lia].
  rewrite firstn1_skipn_repeat by (rewrite E2; lia). reflexivity.
Qed.

Section FILLRD.
  Variables (segs : list Segment) (M : word -> option byte) (sp thr v72 v80 : word) (RIz slot : Z).
  Hypothesis Hsp : 4096 <= U sp /\ U sp < 2 ^ 63.
  Hypothesis Hslot : 0 <= slot < 2 ^ 63.
  Hypothesis HT : U thr + 4096 <= 2 ^ 63.
  Hypothesis HRI : 0 <= RIz /\ RIz + 128 <= 2 ^ 63.
  #[local] Abbreviation SH := (slot / 8 + 0x7fff8000).
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 128.
  Hypothesis HTSH : U thr + 4096 <= SH \/ SH + 2 ^ 15 <= U thr.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.

  Lemma pam_3_fill : forall (vst : word) SPB c mu (i : Z), 0 <= i < 2 ^ 15 ->
    rdn segs (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu) (Z_to_bv 64 (SH + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
  Proof using HRSH HTSH HSSH HRI HT Hslot Hsp.
    intros vst SPB c mu i Hi. destruct Hsp as [SP1 SP2]. destruct HRI as [R0 R1].
    assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite <- (psfill_fill segs M (at_ sp (-64)) (Z_to_bv 64 0x50f10) (Z_to_bv 64 RIz) (at_ thr 2768) (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                  (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)) slot i Hslot Hi).
    rewrite <- pam_1_eq. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
    (lazymatch goal with |- ?G => let G' := eval unfold pam_3 in G in change_no_check G' end). rewrite pf_ms_outside by lia. rewrite pam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). reflexivity.
  Qed.

  Hypothesis HSSHe : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 112.
  Lemma eam_3_fill : forall (s4x s5x : word) mfa (i : Z), 0 <= i < 2 ^ 15 ->
    rdn segs (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa) (Z_to_bv 64 (SH + i)) 1 = Some [cbyte (Z_to_bv 64 250)].
  Proof using HSSHe HRSH HTSH HSSH HRI HT Hslot Hsp.
    intros s4x s5x mfa i Hi. destruct Hsp as [SP1 SP2]. destruct HRI as [R0 R1].
    assert (0 <= slot / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    rewrite <- (psfill_fill segs M (at_ sp (-48)) (Z_to_bv 64 0x4eb54) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4x s5x slot i Hslot Hi).
    rewrite <- eam_1_eq. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
    (lazymatch goal with |- ?G => let G' := eval unfold eam_3 in G in change_no_check G' end). rewrite efs_ms_outside by lia. rewrite eam_2_eq, gts2_outside by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]). reflexivity.
  Qed.
End FILLRD.
End AsAllocM8z.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMHypR.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 AsAllocMHyp.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Lemma icmc_cache_max : forall i, 1 <= i <= 30 -> icmc i = cache_max i /\ iccs i = csize i.
Proof.
  intros i Hi.
  assert (C : forall k : nat, (k < 30)%nat -> icmc (Z.of_nat k + 1) = cache_max (Z.of_nat k + 1) /\ iccs (Z.of_nat k + 1) = csize (Z.of_nat k + 1)).
  { intros k Hk. do 30 (destruct k as [|k]; [split; vm_compute; reflexivity|]). lia. }
  destruct (C (Z.to_nat (i - 1)) ltac:(lia)) as [A B]. rewrite Z2Nat.id in A, B by lia. replace (i - 1 + 1) with i in A, B by lia. exact (conj A B).
Qed.

Section REFILLK.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variables (st : ast) (Lc FF : list (Z * Z)) (M : mem) (mdl : Model) (n : Z).
  Hypothesis W : WF bt st Lc FF.
  Hypothesis RP : Rep bt st Lc FF M mdl.
  Hypothesis Hn : 1 <= n <= 64512.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation SG := (bt_segs bt).
  Definition rk_c : Z := class_of (needed n).
  #[local] Abbreviation c := rk_c.
  Definition rk_fl : list Z := r_free (a_reg st c).
  Definition rk_len : Z := Z.of_nat (length rk_fl).
  Definition rk_m : Z := cache_hint c.
  Hypothesis HC0 : a_cache st c = [].
  Hypothesis Hm : rk_m <= rk_len.

  Definition rk_faf (j : Z) : Z := nth (Z.to_nat j) rk_fl 0.





  Lemma rk_c_range : 1 <= c <= 30.
  Proof using Hn. (lazymatch goal with |- ?G => let G' := eval unfold rk_c in G in change_no_check G' end). pose proof (needed_facts n Hn) as [N1 N2]. apply class_of_range. lia. Qed.






  (* [comment removed for export] *)
  Lemma rk_cells :
    cellZ SG M (T + T_PC + PC_SZ * c) 4 0
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 4) 4 (if a_cinit st then cache_max c else 0)
    /\ cellZ SG M (T + T_PC + PC_SZ * c + 8) 8 (if a_cinit st then csize c else 0)
    /\ cellZ SG M (reginfo bt c) 8 0 /\ cellZ SG M (reginfo bt c + 16) 8 rk_len /\ writableZ SG M (reginfo bt c) (reginfo bt c + 128)
    /\ (forall j, 0 <= j < rk_len -> cellZ SG M (fa_beg SBEG c + 4 * j) 4 (rk_faf j) /\ 0 <= rk_faf j < 2 ^ 32)
    /\ writableZ SG M (region_beg SBEG c) (region_beg SBEG c + r_mapped_user (a_reg st c))
    /\ writableZ SG M T (T + PG).
  Proof using HC0 Hn RP W mdl FF Lc RC.
    pose proof rk_c_range as Hc.
    pose proof RP as (R1 & R2 & R3 & R4 & _). destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & TW & _).
    destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite HC0 in P1. cbn [length Z.of_nat] in P1.
    destruct (R4 c Hc) as [(G1 & _ & G3 & _ & _ & _ & _ & _ & _ & GW) (F1 & F2 & F3)]. fold rk_fl in G3. fold rk_len in G3.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _). fold rk_fl in Y9.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact G1|]. split; [exact G3|]. split; [exact GW|].
    split; [| exact (conj F3 TW)].
    intros j Hj.
    assert (NTH : nth_error rk_fl (Z.to_nat j) = Some (rk_faf j)).
    { (lazymatch goal with |- ?G => let G' := eval unfold rk_faf in G in change_no_check G' end). destruct (nth_error rk_fl (Z.to_nat j)) as [v|] eqn:E.
      - f_equal. symmetry. apply nth_error_nth. exact E.
      - exfalso. apply nth_error_None in E. unfold rk_len in Hj. lia. }
    split.
    - pose proof (F1 (Z.to_nat j) (rk_faf j) NTH) as X. rewrite Z2Nat.id in X by lia. exact X.
    - apply (proj1 (Y9 (rk_faf j) ltac:(eapply nth_error_In; exact NTH))).
  Qed.

  (* [comment removed for export] *)
  Lemma rk_geom :
    0 < SBEG /\ SBEG mod 2 ^ 16 = 0 /\ AS_HEAPLO <= SBEG /\ SBEG + KSPACE + PG <= CEIL
    /\ (T + PG <= SBEG \/ SBEG + KSPACE + PG <= T)
    /\ (bt_tctx bt + 0x10000 <= SBEG \/ SBEG + KSPACE + PG <= bt_tctx bt)
    /\ reginfo bt c = SBEG + KSPACE + 128 * c /\ fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384
    /\ 4 * rk_len <= r_mapped_fa (a_reg st c) <= 2 ^ 29 /\ 0 <= rk_len
    /\ region_beg SBEG c = SBEG + c * 2 ^ 32 /\ 0 <= r_mapped_user (a_reg st c) /\ region_beg SBEG c + r_mapped_user (a_reg st c) <= fa_beg SBEG c
    /\ 0 < T /\ T + PG <= CEIL /\ 0 < bt_tctx bt /\ bt_tctx bt + 0x10000 <= CEIL.
  Proof using Hn W FF Lc.
    pose proof rk_c_range as Hc.
    pose proof (fixed_facts bt st Lc FF W) as (X1 & X2 & X3 & X4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    destruct (space_facts bt st Lc FF W) as ((SP1 & SP2 & SP3 & _ & _) & SP6 & SP7 & SP8 & SPH).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _ & IN6 & R6a & R6b & IN8 & INFS & INT & INN & INS & INC & _) & _).
    pose proof (space_vs_fixed bt st Lc FF W _ _ INT ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end); lia)) as TS.
    pose proof (space_vs_fixed bt st Lc FF W _ _ INC ltac:((lazymatch goal with |- ?G => let G' := eval unfold KSPACE in G in change_no_check G' end); lia)) as CS.
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
    fold rk_fl in E7. fold rk_len in E7.
    split; [lia|]. split; [exact S3|]. split; [lia|]. split; [exact S2|]. split; [exact TS|]. split; [exact CS|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold reginfo, KSPACE in G in change_no_check G' end); reflexivity|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity|].
    split; [lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold rk_len in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end); reflexivity|]. split; [lia|]. split; [lia|].
    exact (conj X1 (conj X2 (conj X3 X4))).
  Qed.

























End REFILLK.
End AsAllocMHypR.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y AsAllocM8z AsAllocM8pa AsAllocM8La AsAllocM8Lk.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 4096 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Lemma pos_mod4096 : forall t, 0 < t -> t mod 4096 = 0 -> 4096 <= t /\ t mod 8 = 0.
Proof. intros t H0 Ht. lia. Qed.
Lemma mod8_of_4096_sum : forall x y, x mod 4096 = 0 -> y mod 4096 = 0 -> (x + y) mod 8 = 0.
Proof. intros x y Hx Hy. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Definition famap_ledger (st : ast) (c : Z) (mdl mdl' : Model) : Prop :=
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    (r_fhole (a_reg st c) = false -> vm_maps (m_vmmaps mdl') = vm_maps (m_vmmaps mdl))
    /\ (r_fhole (a_reg st c) = true -> Permutation (vm_maps (m_vmmaps mdl')) ((Z_to_bv 64 lo, Z_to_bv 64 KFAMAP) :: vm_maps (m_vmmaps mdl)))
    /\ (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
    /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a /\ ~ (lo <= a < lo + KFAMAP))
    /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0 /\ 0 < bv_unsigned (fst iv)
                                   /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                   /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv)))
              (m_vm_lazy mdl')
    /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
    /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
    /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl)
    /\ eager_used mdl' <= eager_used mdl + KFAMAP.

  (* [comment removed for export] *)
  Definition N3F_stmt : Prop := forall st Lc FF M0 mdl c,
    WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> 1 <= c <= 30 -> r_fhole (a_reg st c) = false ->
    r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 -> BackingAlgebra.model_ivs_wf mdl -> m_halted mdl = None -> a_kact st <= KCAP ->
    let lo := fa_beg SBEG c + r_mapped_fa (a_reg st c) in
    let addr : word := Z_to_bv 64 lo in let size : word := Z_to_bv 64 KFAMAP in
    let A2 := a_aa st ++ [(sh_lo lo, sh_lo lo + KFAMAP / 8)] in
    let OK := fixedin_ok_model 3 (Z_to_bv 64 50) addr size in let DS := fixedin_destroyed_model addr size in
    A_wf A2
    /\ (forall mdlm, same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
          U addr + U size <= alloc_top (m_vmmaps mdlm) /\ alloc_top (m_vmmaps mdlm) < two_pow_64
          /\ region_free (vm_reserved (m_vmmaps mdlm)) addr size = true /\ map_contains (vm_maps (m_vmmaps mdlm)) addr size = true
          /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 50) mdlm addr size = true
          /\ m_halted (OK mdlm) = None /\ MInv (a_aa st) (OK mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (OK mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true)
          /\ m_halted (DS mdlm) = None /\ MInv (a_aa st) (DS mdlm)
          /\ (forall p, page_in_ranges p (m_vm_lazy (DS mdlm)) = true -> page_in_ranges p (m_vm_lazy mdl) = true))
    /\ (forall mdlm mdl4, same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl4 -> MInv (a_aa st) mdl4 -> MInv A2 mdl4)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (OK mdlm) mdl' ->
          famap_ledger st c mdl mdl' /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None)
    /\ (forall mdlm mdl', same_but_materialized mdl mdlm -> same_but_materialized (DS mdlm) mdl' ->
          ledger_destroyed bt mdl mdl' lo KFAMAP /\ eager_used mdl' <= eager_used mdl
          /\ same_except_vm mdl mdl' /\ lazy_kept IA Lc FF mdl mdl' /\ BackingAlgebra.model_ivs_wf mdl' /\ m_halted mdl' = None).
  Hypothesis N3F : N3F_stmt.


  (* [comment removed for export] *)
  Lemma writableZ_of_def : forall (M : mem) lo hi, 0 <= lo -> hi < 2 ^ 64 -> (forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None) -> writableZ ASEGS M lo hi.
  Proof using.
    intros M lo hi L0 H1 DEF i Hi. split; [exact (DEF i Hi)|]. apply store_ok_of_all; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. assert (x = Z_to_bv 64 i) as -> by (apply bv_eq; rewrite u_Z2bv by lia; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). pose proof (DEF i Hi) as Dd. destruct (M (Z_to_bv 64 i)); [discriminate | exfalso; exact (Dd eq_refl)].
  Qed.
  Lemma lazy_kept_sbm : forall Lc FF mdl mdl', same_but_materialized mdl mdl' -> lazy_kept IA Lc FF mdl mdl'.
  Proof using.
    intros Lc FF mdl mdl' S a _. pose proof (same_but_materialized_frame mdl mdl' S) as (_ & _ & E & _). (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite E. reflexivity.
  Qed.
  Lemma halted_sbm : forall mdl mdl', same_but_materialized mdl mdl' -> m_halted mdl = None -> m_halted mdl' = None.
  Proof using. intros mdl mdl' S H. pose proof (same_but_materialized_frame mdl mdl' S) as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact H. Qed.

  Theorem popBf_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_fhole (a_reg st c) = false -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ ASEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x4ea98%bv : word) M rom) mdl) Qok Qf.
  Proof using N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W RX HALT MW FH ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mfa in E6, E7, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _). fold r mfa in Y5, Y6.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x65d000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x65d000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x65d000).
    { do 32 (destruct CREST as (_ & CREST)). destruct CREST as (A1 & A2 & A3 & A4 & _ & _ & _ & A8 & A9). repeat split; assumption. }
    destruct G_consts as (Gs1 & Gs2 & Gp1 & Gp2 & Gt1 & Gt2).
    pose proof PCELLS as (PC_rel & PC_rib & PC_pre & PC_dpm & PC_lim).
    set (RIz := reginfo bt c) in *. set (rbeg := region_beg SBEG c) in *.
    assert (ERI : RIz = SBEG + KSPACE + 128 * c) by reflexivity.
    assert (ERB : rbeg = SBEG + c * 2 ^ 32) by ((lazymatch goal with |- ?G => let G' := eval unfold rbeg, region_beg, KREGION in G in change_no_check G' end); reflexivity).
    assert (ELO : lo = rbeg + 0xE0000000 + mfa) by ((lazymatch goal with |- ?G => let G' := eval unfold lo, fa_beg, KFAOFF in G in change_no_check G' end); fold rbeg; reflexivity).
    assert (ESH : sh_lo lo = (rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000) by (rewrite ELO; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) (F1 & F2 & F3)]. fold r RIz mfa in G24, GW.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    (* [comment removed for export] *)
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    unfold KSPACE, PG, KFAMAP, KFAOFF, AS_HEAPLO, AS_LO in *.
    assert (SLOT : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37 /\ lo mod 8 = 0).
    { split; [rewrite ELO, ERB; lia|]. split; [rewrite ELO; fold rbeg in E5; unfold fa_beg in E5; lia|].
      (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod8_of_4096_sum; [exact E12 | exact E14]. }
    destruct SLOT as (SL0 & SL1 & SL8).
    assert (SLa : 17594333495296 <= lo) by lia.
    assert (SLb : lo + 2 ^ 18 <= CEIL) by lia.
    destruct (sh_band lo (2 ^ 18) SLa ltac:(lia) SLb ltac:(reflexivity)) as (SHB0 & SHB1 & SHB2).
    unfold AS_GAPHI, AS_HEAPLO in SHB0, SHB1. replace (2 ^ 18 / 8) with (2 ^ 15) in SHB1, SHB2 by reflexivity.
    set (SH := sh_lo lo) in *. assert (ESH' : SH = SB + lo / 8) by reflexivity. rewrite <- ESH' in SHB0, SHB1, SHB2.
    (* [comment removed for export] *)
    assert (YIMG : forall z, XL c z -> ~ (AIMGLO <= z < AIMGHI)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (XOFF z Hx))) | fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    (* [comment removed for export] *)
    destruct (N3F st Lc FF M0 mdl c W RP Hc FH ROOM MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK & LEDDS).
    fold r mfa lo SH in AWF2, NODEF, BUD, LEDOK, LEDDS. unfold KFAMAP in AWF2, NODEF, BUD, LEDOK, LEDDS.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := fixedin_ok_model 3 (Z_to_bv 64 50) addr size) in *. set (DSm := fixedin_destroyed_model addr size) in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    (* [comment removed for export] *)
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    set (thr := Z_to_bv 64 T : word).
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    apply (efs_map_arm_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz rbeg tot mfa PGP 0x1990a8 T 0 Qok Qf OKm (fun m => m) DSm).
    all: try (first [exact H1 | exact H2 | exact H4 | exact H3 | exact H10 | exact H11 | exact H12 | exact H13 | exact H8 | exact H9 | exact H18 | exact H19 | exact H20 | exact H21
                    | exact Hret | exact Htot | exact HALT | exact Bw1 | exact Bw2 | exact Hneed]).
    - (* [comment removed for export] *) lia.
    - split; [lia | exact Y6].
    - exact ROOM.
    - split; [lia|]. split; [lia | exact E11].
    - lia.
    - lia.
    - lia.
    - apply (writableZ_sok M (U sp - 448) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (RIz + 24) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G24].
    - change (1064728 + 56) with 0x103f50. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1674984 + 260) with 0x1991ac. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1674984 + 144) with 0x199138. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - left. rewrite <- ELO. lia.
    - apply HOFF. intros z Hz. apply NHri. lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply HOFF. intros z Hz. apply NHs; lia.
    - apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10 G11 G12 G13 G14 G15 Qok' Qf' K1.
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & N5 & _).
      apply (node1_of_fixedin3_s r1 _ rom mdlm addr size Qok' Qf' HLm G10 G11 G12 G13 G14 G15); [ | | | | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | exact K1].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod4096_sum; [exact E12 | exact E14].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & HDS & MDSI & LZDS).
      split; [| split].
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
      + split; [exact HDS|]. split; [| exact MDSI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZDS).
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & _ & LZOK & _).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG lo (Z_to_bv 64 322388) (at_ sp (-48)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - eapply Forall_impl; [| exact asan_poison_cells_img]. cbv beta. intros c0 [_ Hc0]. exact Hc0.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl W RP D YIMG YCTX (at_ (at_ sp (-48)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, asan_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q4 Q3.
      rewrite <- ELO.
      destruct (LEDOK mdlm mdl5 SBm SB5) as (LED & SEV & LK & MW5 & HL5).
      set (MR := efs_mr M sp ra s0v s1v s2v s3v s4v s5v RIz lo mfa PGP).
      set (M' := eam_3 MR sp s4v s5v thr v72 v80 RIz lo mfa).
      assert (ESH2 : SH = lo / 8 + 2147450880) by (rewrite ESH'; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia).
      assert (OUTM : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> (U a < SH \/ SH + 2 ^ 15 <= U a) ->
                 (U a < T + 2872 \/ T + 2888 <= U a) -> (U a < RIz + 24 \/ RIz + 32 <= U a) -> M' a = M a).
      { intros a X1 X2 X3 X4 X5. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end).
        rewrite (eam_3_outside MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia) ltac:(lia) a
                   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear - X1; lia)
                   ltac:(rewrite <- ESH2; exact X3) ltac:(rewrite UT; exact X4) X5).
        (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_outside; [lia | lia | exact X1 | exact X2]. }
      assert (GRM : mem_grows M M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). eapply mem_grows_trans; [| apply eam_3_grows]. (lazymatch goal with |- ?G => let G' := eval unfold MR in G in change_no_check G' end). apply efs_mr_grows. }
      assert (DEFSL : forall a : word, lo <= U a < lo + 2 ^ 18 -> M' a <> None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply eam_3_grows. (lazymatch goal with |- ?G => let G' := eval unfold MR, efs_mr in G in change_no_check G' end). apply wbytes_grows. (lazymatch goal with |- ?G => let G' := eval unfold zfill, zmem in G in change_no_check G' end). rewrite !u_Z2bv by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. discriminate. }
      assert (WRIM : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                 \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ (SH <= U a < SH + 2 ^ 15)
                      \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32))
                     \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a) /\ (U a < SH \/ SH + 2 ^ 15 <= U a)
                         /\ (U a < T + 2872 \/ T + 2888 <= U a) /\ (U a < RIz + 24 \/ RIz + 32 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3 & O4 & O5)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3 O4 O5))].
        split; [exact IN|].
        destruct IN as [I1 | [I2 | [I3 | [I4 | I5]]]].
        - apply GRM. destruct (WSTK (U a) I1) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - exact (DEFSL a I2).
        - apply GRM. rewrite <- (Z_to_bv_bv_unsigned _ a). apply (pk_shadow_def bt (XL c) st Lc FF M M0 mdl RP D). (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). right. clear - I3 SHB0 SHB1. lia.
        - apply GRM. destruct (TWR (U a) ltac:(clear - I4; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        - apply GRM. destruct (WRIM (U a) ltac:(clear - I5; lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      assert (W' : WF bt (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF).
      { apply (WF_meter bt (op_famap st c) Lc FF 0 [(SH, SH + 2 ^ 18 / 8)] 0 (OPS_WF_famap_pf bt st Lc FF c W Hc ROOM FAQ)); lia. }
      assert (RX' : RepX bt (XL c) (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 448 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 24 <= z < RIz + 32))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REP_famap_pf bt st Lc FF N0 N0' mdl mdl5 c W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_famap, fslot in G in change_no_check G' end). fold r mfa lo RIz SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mfa RIz. rewrite (rdn_ext ASEGS 8 N0' M' (Z_to_bv 64 (RIz + 24))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (eam_3_mfa ASEGS MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r mfa lo SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext ASEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (eam_3_fill ASEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) ltac:(rewrite <- ESH2; right; lia) s4v s5v mfa (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [| exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q4 | exact Q3].
      intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. fold RIz. clear - F. lia.
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. cbv beta in SB5.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MK := MKK) end.
      pose proof (same_but_materialized_trans _ _ _ SBm SB5) as SBK.
      assert (OUTK : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> MK a = M a).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (GRK : mem_grows M MK).
      { (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [| apply wbytes_grows]). eapply mem_grows_trans; [apply efs_m0_grows | apply mfi_m1_grows]. }
      assert (FOOTK : forall a : word, MK a <> M a -> (U sp - 448 <= U a < U sp) /\ MK a <> None).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (U a < U sp - 448 \/ U sp <= U a)) by (clear; lia).
        destruct IN as [IN | O1]; [| exfalso; exact (Ha (OUTK a O1))]. split; [exact IN|].
        apply GRK. destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step bt (XL c) st Lc FF M MK mdl mdl5 W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
    - (* [comment removed for export] *)
      intros r0 r' mdlm mdl5 SBm MIm SB5 MI5 AG POST. rewrite <- ELO.
      match goal with |- katD _ (mkCfg (mkst _ _ ?MKK _) _) _ => set (MD := MKK) end.
      destruct (LEDDS mdlm mdl5 SBm SB5) as (LD & EAG & SEV & LK & MW5 & HL5).
      assert (OUTD : forall a : word, (U a < U sp - 448 \/ U sp <= U a) -> (U a < lo \/ lo + 2 ^ 18 <= U a) -> MD a = M a).
      { intros a Ha Hb. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        rewrite unfill_out by (rewrite !u_Z2bv by lia; exact Hb).
        rewrite mfi_m1_outside by (rewrite ?at_u by lia; lia). apply efs_m0_outside; lia. }
      assert (SLD : forall a : word, lo <= U a < lo + 2 ^ 18 -> MD a = None).
      { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        (lazymatch goal with |- ?G => let G' := eval unfold unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
      assert (STD : forall a : word, U sp - 448 <= U a < U sp -> MD a <> None).
      { intros a Ha. destruct (decide (MD a = M a)) as [E | NE]; [rewrite E; destruct (WSTK (U a) Ha) as [Dd _]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd|].
        (* [comment removed for export] *)
        unfold MD in NE |- *.
        set (MU := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) _) in *.
        assert (GU : forall x : word, U sp - 448 <= U x < U sp -> MU x <> None).
        { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MU in G in change_no_check G' end). rewrite unfill_out by (rewrite !u_Z2bv by lia; lia).
          apply mfi_m1_grows. apply efs_m0_grows. destruct (WSTK (U x) Hx) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
        do 2 apply wbytes_grows. exact (GU a Ha). }
      assert (FOOTD : forall a : word, MD a <> M a -> ((U sp - 448 <= U a < U sp) /\ MD a <> None) \/ (lo <= U a < lo + 2 ^ 18)).
      { intros a Ha. assert (IN : (U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + 2 ^ 18) \/ ((U a < U sp - 448 \/ U sp <= U a) /\ (U a < lo \/ lo + 2 ^ 18 <= U a))) by (clear; lia).
        destruct IN as [IN | [IN | [O1 O2]]]; [left; split; [exact IN | exact (STD a IN)] | right; exact IN | exfalso; exact (Ha (OUTD a O1 O2))]. }
      assert (W1 : WF bt (op_fhole st c) Lc FF) by (apply (WF_fhole bt st Lc FF c Hc ROOM W)).
      apply (CONT0 r0 r' MD mdl5 (op_fhole st c) (or_intror eq_refl) W1); [ | exact SEV | exact LK | exact MW5 | exact HL5 | | exact AG | exact POST].
      + (* [comment removed for export] *)
        set (N1 := unfill (Z_to_bv 64 lo) (Z_to_bv 64 (2 ^ 18)) M0).
        assert (RP1 : Rep bt (op_fhole st c) Lc FF N1 mdl5).
        { apply (OPS_REP_fhole_pf bt st Lc FF M0 N1 mdl mdl5 c W RP Hc FH ROOM); [ | exact LD | exact MI5 | exact EAG].
          intros a Ha. unfold N1, unfill in Ha |- *. rewrite !u_Z2bv in Ha |- * by lia. (lazymatch goal with |- ?G => let G' := eval unfold fslot in G in change_no_check G' end). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
          destruct (Z.leb_spec lo (U a)); destruct (Z.ltb_spec (U a) (lo + 2 ^ 18)); cbn [andb] in Ha |- *; first [split; [lia | reflexivity] | exfalso; exact (Ha eq_refl)]. }
        set (N := fun a : word => if Z_le_dec lo (U a) then (if Z_lt_dec (U a) (lo + 2 ^ 18) then None else if decide (M a = M0 a) then MD a else M0 a)
                                  else if decide (M a = M0 a) then MD a else M0 a).
        assert (N1in : forall a : word, lo <= U a < lo + 2 ^ 18 -> N1 a = None).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1, unfill in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
        assert (N1out : forall a : word, (U a < lo \/ lo + 2 ^ 18 <= U a) -> N1 a = M0 a).
        { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold N1 in G in change_no_check G' end). apply unfill_out. rewrite !u_Z2bv by lia. exact Ha. }
        exists N. split.
        * apply (Rep_frame bt (op_fhole st c) Lc FF N1 N mdl5 W1 RP1). intros a Ha. unfold N in Ha |- *.
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. symmetry. apply N1in. lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_fhole st c) Lc FF (U a) W1 RCa). lia.
          -- rewrite (N1out a ltac:(lia)) in Ha. destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
             rewrite <- E in Ha. destruct (FOOTD a Ha) as [[IN Dd] | IN]; [| lia]. split; [|exact Dd].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia (op_fhole st c) Lc FF (U a) W1 RCa). lia.
        * intros a Ha. unfold N in Ha.
          assert (CASE : forall (E : M a <> M0 a), XL c (U a) /\ MD a <> None).
          { intros NE. destruct (D a NE) as [HX Dd]. split; [exact HX|].
            destruct (decide (MD a = M a)) as [EQ2 | NE2]; [rewrite EQ2; exact Dd|].
            destruct (FOOTD a NE2) as [[_ Dd2] | IN]; [exact Dd2 | exfalso; exact (XSL (U a) IN HX)]. }
          destruct (Z_le_dec lo (U a)) as [L1|L1]; [destruct (Z_lt_dec (U a) (lo + 2 ^ 18)) as [L2|L2]|].
          -- exfalso. apply Ha. apply SLD. lia.
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
          -- destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl) | exact (CASE NE)].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (FOOTD a Ha).
  Qed.


End L3.
End WithCeil.
