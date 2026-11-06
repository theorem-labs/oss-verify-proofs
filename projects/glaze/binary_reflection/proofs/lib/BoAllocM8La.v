(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8v.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
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
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

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
    rdn BSEGS M (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) -> rdn BSEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)) ->
    rdn BSEGS M (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) -> rdn BSEGS M (Z_to_bv 64 (RIz + 40)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    rdn BSEGS M (Z_to_bv 64 (RIz + 56)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
    store_ok BSEGS M (Z_to_bv 64 RIz) 128 = true -> store_ok BSEGS M (Z_to_bv 64 (FAB + 4 * nf)) (Z.to_nat (4 * newn)) = true ->
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    hid_off Hd RIz 128 -> hid_off Hd (FAB + 4 * nf) (4 * newn) -> hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        pf_post1 sp ra s0v s1v s2v s3v s4v s5v s6v regs r ->
        katwD BSEGS (mkCfg (mkst r ra (pf_mc M RIz top au (csize c) nf newn) rom) mdlm) Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x519d8 : word) M rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs M rom model sp ra s0v s1v s2v s3v s4v s5v s6v RIz SPB c au mu nf Qok Qf newn FAB top
           HR H10 H9 H19 H20 Hsp Hret Hc Hau Hnf HSPB HRI Rau Rnf Rmu Ram Rmm SOKRI SOKfa Sra Ss0 Ss1 Ss2 Ss3 Ss4 Ss5 Ss6
           HDRI HDfa HDf HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. pose proof (csize_pos c Hc) as [CS1 CS2].
    assert (N0 : 0 <= newn) by ((lazymatch goal with |- ?G => let G' := eval unfold newn in G in change_no_check G' end); apply Z.div_pos; lia).
    assert (TOPE : top - 4 * newn = FAB + 4 * nf) by ((lazymatch goal with |- ?G => let G' := eval unfold top, FAB, newn in G in change_no_check G' end); lia).
    assert (RIr : forall (k : Z) v, 0 <= k -> k + 8 <= 128 -> rdn BSEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v ->
               rdn BSEGS (mrestrict Hd M) (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]]. }
    assert (SPr : forall (k : Z) v, -64 <= k -> k + 8 <= 0 -> rdn BSEGS M (at_ sp k) 8 = Some v -> rdn BSEGS (mrestrict Hd M) (at_ sp k) 8 = Some v).
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
      apply (katwD_msteps_acct BSEGS Hd HOFFSEG WX A (mkst regs (0x519d8 : word) M rom)
               (mkst r ra (mrestrict Hd (pf_mc M RIz top au (csize c) nf newn)) rom) model Qok Qf LC AWF MI HALT).
      { rewrite mk_restrict_mkst.
        rewrite <- (pf_mc_mrestrict Hd M RIz top au (csize c) nf newn N0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HDfa' HDRI).
        exact RUN. }
      intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
      replace (RiscvSemantics.ms_mem (mkst regs (0x519d8 : word) M rom)) with M by reflexivity.
      rewrite (mk_munrestrict_same Hd M _ HIDSAME).
      exact (CONT r mdlm SBMm MIm POST).
  Qed.
End LIFTS.
End FPGen.
End BoAllocM8v.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
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
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
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
    rdn BSEGS M0 (Z_to_bv 64 z) k = Some v -> rdn BSEGS M (Z_to_bv 64 z) k = Some v.
  Proof using.
    intros Y M M0 D z k v Z0 Z1 OFF Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply (repx_off Y M M0 D). apply OFF. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma repx_wr : forall (Y : Z -> Prop) (M M0 : mem), (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
    forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> writableZ BSEGS M0 lo hi -> writableZ BSEGS M lo hi.
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
  Lemma writableZ_sok : forall (M : mem) lo hi (a : word) (n : nat), writableZ BSEGS M lo hi -> lo <= U a -> U a + Z.of_nat n <= hi -> hi < 2 ^ 64 ->
    store_ok BSEGS M a n = true.
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
    - destruct K as [K _]. rewrite BT_ia in K. cbn [ia_img_lo ia_img_hi both_addrs] in K. lia.
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
    rdn BSEGS M (at_ sp (-8)) 8 = Some (LE8 ra) -> rdn BSEGS M (at_ sp (-16)) 8 = Some (LE8 s0v) -> rdn BSEGS M (at_ sp (-24)) 8 = Some (LE8 s1v) ->
    rdn BSEGS M (at_ sp (-32)) 8 = Some (LE8 s2v) -> rdn BSEGS M (at_ sp (-40)) 8 = Some (LE8 s3v) -> rdn BSEGS M (at_ sp (-48)) 8 = Some (LE8 s4v) ->
    rdn BSEGS M (at_ sp (-56)) 8 = Some (LE8 s5v) -> rdn BSEGS M (at_ sp (-64)) 8 = Some (LE8 s6v) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_carve SBEG st c) Lc FF -> RepX bt (XL c) (op_carve SBEG st c) Lc FF M' mdl' -> same_but_materialized mdl mdl' ->
        (forall a : word, M' a <> M a ->
            ((fa_beg SBEG c + 4 * nf <= U a < fa_beg SBEG c + 4 * (nf + newn)) \/ (reginfo bt c + 16 <= U a < reginfo bt c + 128)) /\ M' a <> None) ->
        pf_post1 sp ra s0v s1v s2v s3v s4v s5v s6v regs r' ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x519d8%bv : word) M rom) mdl) Qok Qf.
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
    assert (RDRI : forall k v, 8 <= k -> k + 8 <= 128 -> rdn BSEGS M0 (Z_to_bv 64 (RIz + k)) 8 = Some v -> rdn BSEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. apply (repx_rd (XL c) M M0 D (RIz + k) 8 v); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact Hr]. }
    assert (WRI : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
    assert (WFA : writableZ BSEGS M FAB (FAB + r_mapped_fa r)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact F2]).
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
                   rdn BSEGS M' (Z_to_bv 64 z) k = Some v -> rdn BSEGS N0' (Z_to_bv 64 z) k = Some v).
        { intros z k v Z0 Z1 IN Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
          apply EQF. clear - Hx IN. lia. }
        destruct (pf_mc_rd BSEGS M RIz top (r_alloc_user r) (csize c) nf newn N0 ltac:(lia) ltac:(lia) ltac:(lia)) as (P16 & P32 & P68 & PENT).
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
