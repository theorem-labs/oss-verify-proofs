(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8pb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.



Section FPGen.
Context {fx : FPState}.
Section PFNOMAP.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.

  Theorem pf_nomap_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp : word) (RIz SPB c req au mu nf : Z) (Qok Qf : config -> Prop),
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> au + csize c * req <= mu -> 0 <= nf <= 2 ^ 27 ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64) -> (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64) ->
    store_ok BSEGS mem (at_ sp (-64)) 64 = true ->
    rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn BSEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)) ->
    hid_off Hd (0x10ab58 + 32) 8 -> hid_off Hd RIz 128 -> hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x519d8 ->
        getr r 10 = Z_to_bv 64 0x10ab58 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
        getr r 13 = Z_to_bv 64 (nf + (mu - au) / csize c) ->
        getr r 9 = Z_to_bv 64 (nf + (mu - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu - au) / csize c) ->
        getr r 20 = Z_to_bv 64 (mu - au) -> getr r 4 = tp -> getr r 3 = gp ->
        katwD BSEGS (mkCfg (mkst r (0x4f508 : word) (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v) rom) mdlm) Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x51844 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp RIz SPB c req au mu nf Qok Qf
           H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hc Hreq Hau Hno Hnf HSPB HRI Hstk C_sbeg R_au R_mu R_nf
           HDsbeg HDRI HDf HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hau as [[AU0 AU1] AU2].
    set (M0 := pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k < 2 ^ 64 -> hid_off Hd cc (Z.of_nat k) ->
               rdn BSEGS mem (Z_to_bv 64 cc) k = Some v -> rdn BSEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (pf_head_nomap (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu regs
                H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 (conj SP1 SP2) Hc Hreq (conj (conj AU0 AU1) AU2) HSPB (conj RI1 RI2)
                ltac:(rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]])
                (CELLR (0x10ab58 + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDsbeg C_sbeg)
                (CELLR (RIz + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(eapply hid_off_sub; [exact HDRI | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]) R_au)
                (CELLR (RIz + 48) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(eapply hid_off_sub; [exact HDRI | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]) R_mu) Hno)
      as (r1 & RUN1 & PR1 & A10 & A13 & A20 & AG1).
    rewrite pf_m0_mrestrict in RUN1 by (first [lia | exact HDf]). fold M0 in RUN1.
    assert (M0out : forall x : word, (U x < U sp - 64 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_outside; [lia | exact Hx]).
    assert (Rnf0 : rdn BSEGS (mrestrict Hd M0) (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { rewrite rdn_mrestrict; [ | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]].
      rewrite <- R_nf. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply M0out. lia. }
    destruct (pf_efs_call (mrestrict Hd M0) rom sp RIz SPB c au mu nf r1 PR1 A10 A13 A20 (conj SP1 SP2) Hc ltac:(lia) Hnf (conj RI1 RI2) Rnf0)
      as (r2 & RUN2 & PR2 & B1 & B10 & B11 & B12 & B13 & B9 & B19 & B20 & AG2).
    apply (lift_katwD_mem Hd HOFFSEG WX A regs (0x51844 : word) r2 (0x4f508 : word) mem M0 rom model Qok Qf
             ltac:(eapply msteps_trans; [exact RUN1 | exact RUN2])); [ | exact HALT | exact LC | exact AWF | exact MI |].
    - intros a Ha. pose proof (hid_true_off Hd a _ _ Ha HDf) as Z1. apply M0out. lia.
    - intros mdlm SBM MIm. apply (CONT r2 mdlm SBM MIm PR2 B1 B10 B11 B12 B13 B9 B19 B20).
      + rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        exact H4.
      + rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold pf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        exact H3.
  Qed.
End PFNOMAP.
End FPGen.
End BoAllocM8pb.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8Lb.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp BoAllocM8pb OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
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
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variable X : Z -> Prop.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).

  Theorem popBe_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
    (CEIL + 48 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) ->
    4 * tot <= r_mapped_fa (a_reg st c) ->
    writableZ BSEGS M (U sp - 48) (U sp) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> (U sp - 48 <= U a < U sp) /\ M' a <> None) ->
        efs_post sp ra s0v s1v s2v s3v 1 regs r' ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v tot Qok Qf Hc W RX HALT XOFF H1 H2 H11 H13 H8 H9 H18 H19 Hsp Hret Htot ENOUGH WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _).
    unfold KSPACE, PG, KFAMAP in *.
    set (RIz := reginfo bt c) in *. set (r := a_reg st c) in *.
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) _]. fold r RIz in G24.
    rewrite BT_segs in *.
    destruct R14 as (Bw1 & Bw2 & _).
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (XOFF i Hx ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> CEIL <= z -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). left. exact Hr. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (HOFF : forall lo n, 0 <= lo -> lo + n < 2 ^ 64 -> (forall z, lo <= z < lo + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n).
    { intros lo n L0 L1 Hz x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    apply (efs_enough_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs M rom mdl sp ra s0v s1v s2v s3v
             RIz tot (r_mapped_fa r) Qok Qf H1 H2 H11 H13 H8 H9 H18 H19 ltac:(lia) Hret Htot ltac:(lia) ltac:(lia)).
    - apply (writableZ_sok M (U sp - 48) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (RIz + 24) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G24].
    - exact ENOUGH.
    - apply HOFF; [lia | lia | intros z Hz; apply NHs; lia].
    - apply HOFF; [lia | lia | intros z Hz; apply NHri; lia].
    - exact HALT.
    - apply lazy_cover_HID.
    - exact Bw1.
    - exact Bw2.
    - intros r' mdlm SBM MIm POST.
      set (M' := efs_m0 M sp ra s0v s1v s2v s3v).
      assert (FOOTM : forall a : word, M' a <> M a -> (U sp - 48 <= U a < U sp) /\ M' a <> None).
      { intros a Ha.
        assert (IN : U sp - 48 <= U a < U sp).
        { destruct (Z_lt_le_dec (U a) (U sp - 48)) as [C1|C1]; [exfalso; apply Ha; apply efs_m0_outside; lia|].
          destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [lia | exfalso; apply Ha; apply efs_m0_outside; lia]. }
        split; [exact IN|]. apply (efs_m0_grows M sp ra s0v s1v s2v s3v a).
        destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT r' M' mdlm); [ | exact SBM | exact MIm | exact FOOTM | exact POST].
      apply (repx_frame_step bt (XL c) st Lc FF M M' mdl mdlm W RX); [| exact MIm | exact SBM].
      intros a Ha. destruct (FOOTM a Ha) as [IN Dd]. split; [|exact Dd].
      intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
  Qed.

  Theorem popAn_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp : word) (req : Z)
           (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None ->
    In (0x10ab78, 8%nat, SBEG) (bt_consts bt) ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI)) ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 0x10ab58 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (CEIL + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    r_alloc_user r + csize c * req <= r_mapped_user r ->
    writableZ BSEGS M (U sp - 64) (U sp) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> (U sp - 64 <= U a < U sp) /\ M' a <> None) ->
        (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
            rdn BSEGS M' (at_ sp k) 8 = Some (LE8 v)) ->
        pf_regs sp (reginfo bt c) SBEG c r' -> getr r' 1 = Z_to_bv 64 0x519d8 ->
        getr r' 10 = Z_to_bv 64 0x10ab58 -> getr r' 11 = Z_to_bv 64 (reginfo bt c) -> getr r' 12 = Z_to_bv 64 (SBEG + c * 2 ^ 32) ->
        getr r' 13 = Z_to_bv 64 (nf + carve_n r c) -> getr r' 9 = Z_to_bv 64 (nf + carve_n r c) -> getr r' 19 = Z_to_bv 64 (carve_n r c) ->
        getr r' 20 = Z_to_bv 64 (r_mapped_user r - r_alloc_user r) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD BSEGS (mkCfg (mkst r' (0x4f508%bv : word) M' rom) mdl') Qok Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x51844%bv : word) M rom) mdl) Qok Qf.
  Proof using BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp req Qok Qf Hc W RX HALT CSBEG XOFF r nf
           H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hreq NOMAP WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold nf in E7.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & Y2 & Y3 & _). fold r in Y1a, Y1b, Y2, Y3.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. rewrite BT_ia in I1, I2. cbn [ia_img_lo ia_img_hi both_addrs] in I1, I2.
    unfold KSPACE, PG, KUSERMAP, KREGION_EXHAUST in *.
    set (RIz := reginfo bt c) in *.
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G68 & GW) _]. fold r RIz nf in G16, G32, G48.
    pose proof (const_cell bt M0 _ _ _ ltac:(rewrite <- BT_segs; exact R1) CSBEG) as KSB.
    rewrite BT_segs in *.
    destruct R14 as (Bw1 & Bw2 & _).
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XIM : forall i, AIMGLO <= i < AIMGHI -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj2 (XOFF i Hx) Hi) | fold RIz in Hl; lia]. }
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (HOFF : forall lo n, 0 <= lo -> lo + n < 2 ^ 64 -> (forall z, lo <= z < lo + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n).
    { intros lo n L0 L1 Hz x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    assert (RDRI : forall k v, 8 <= k -> k + 8 <= 128 -> rdn BSEGS M0 (Z_to_bv 64 (RIz + k)) 8 = Some v -> rdn BSEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. apply (repx_rd (XL c) M M0 D (RIz + k) 8 v); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact Hr]. }
    apply (pf_nomap_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp
             RIz SBEG c req (r_alloc_user r) (r_mapped_user r) nf Qok Qf
             H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq ltac:(lia) NOMAP ltac:(lia) ltac:(lia) ltac:(lia)).
    - apply (writableZ_sok M (U sp - 64) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (0x10ab58 + 32) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XIM; cbn in Hi; lia | exact KSB].
    - exact (RDRI 32 _ ltac:(lia) ltac:(lia) G32).
    - exact (RDRI 48 _ ltac:(lia) ltac:(lia) G48).
    - exact (RDRI 16 _ ltac:(lia) ltac:(lia) G16).
    - apply HOFF; [lia | lia | intros z Hz; apply NHs; lia].
    - apply HOFF; [lia | lia | exact NHri].
    - apply HOFF; [lia | lia | intros z Hz; apply NHs; lia].
    - exact HALT.
    - apply lazy_cover_HID.
    - exact Bw1.
    - exact Bw2.
    - intros r' mdlm SBM MIm PR D1 D10 D11 D12 D13 D9 D19 D20 D4 D3.
      set (M' := pf_m0 M sp ra s0v s1v s2v s3v s4v s5v s6v).
      assert (FOOTM : forall a : word, M' a <> M a -> (U sp - 64 <= U a < U sp) /\ M' a <> None).
      { intros a Ha.
        assert (IN : U sp - 64 <= U a < U sp).
        { destruct (Z_lt_le_dec (U a) (U sp - 64)) as [C1|C1]; [exfalso; apply Ha; apply pf_m0_outside; lia|].
          destruct (Z_lt_le_dec (U a) (U sp)) as [C2|C2]; [lia | exfalso; apply Ha; apply pf_m0_outside; lia]. }
        split; [exact IN|]. apply (pf_m0_grows M sp ra s0v s1v s2v s3v s4v s5v s6v a).
        destruct (WSTK (U a) IN) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd. }
      apply (CONT r' M' mdlm); [ | exact SBM | exact MIm | exact FOOTM | | exact PR | exact D1 | exact D10 | exact D11 | exact D12 | exact D13 | exact D9 | exact D19 | exact D20 | exact D4 | exact D3].
      + apply (repx_frame_step bt (XL c) st Lc FF M M' mdl mdlm W RX); [| exact MIm | exact SBM].
        intros a Ha. destruct (FOOTM a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
      + intros k v Hin. apply (pf_slots_ext M' M sp ra s0v s1v s2v s3v s4v s5v s6v k v ltac:(lia) ltac:(lia)); [intros x _; reflexivity | exact Hin].
  Qed.
End L3.
End WithCeil.
End BoAllocM8Lb.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Ld. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La BoAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Ld.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lch. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lch.
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




Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  Hypothesis N3F : N3F_stmt bt.
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FH_stmt bt.     (* [comment removed for export] *)
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation XL := (XL bt X).
  #[local] Abbreviation IA := (bt_ia bt).

  (* [comment removed for export] *)
  Lemma popF_katD :
    forall (Y : Z -> Prop) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v : word) (Q : config -> Prop),
    WF bt st Lc FF -> RepX bt Y st Lc FF M mdl -> m_halted mdl = None ->
    getr regs 2 = at_ sp (-64) -> getr regs 10 = Z_to_bv 64 0 -> ret_ok ra -> (CEIL + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
        rdn BSEGS M (at_ sp k) 8 = Some (LE8 v)) ->
    (forall (r' : bvmap 5 word) mdl', RepX bt Y st Lc FF M mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v regs r' -> katD BSEGS (mkCfg (mkst r' ra M rom) mdl') Q) ->
    katD BSEGS (mkCfg (mkst regs (0x519d8%bv : word) M rom) mdl) Q.
  Proof using BT_ia.
    intros Y st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v Q W RX HALT H2 H10 Hret [SP1 SP2] SL CONT.
    pose proof ceil_rng as CR. pose proof (u64_range sp) as Hspr. pose proof RX as (M0 & RP & D).
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _). destruct R14 as (Bw1 & Bw2 & _).
    set (Hd := HID st mdl).
    assert (HDf : hid_off Hd (U sp - 64) 64).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply (HID_off_zone bt st mdl (U x) R13); [lia | left; lia]. }
    apply (pf_fail_efs_katD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v s6v Q
             H2 H10 Hret ltac:(lia)
             (SL (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
             (SL (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-48) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-56) s5v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)) (SL (-64) s6v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10))
             HDf HALT (lazy_cover_HID st mdl) Bw1 Bw2).
    intros r' mdlm SBM MIm POST. apply (CONT r' mdlm); [ | exact SBM | exact MIm | exact POST].
    apply (repx_frame_step bt Y st Lc FF M M mdl mdlm W RX); [| exact MIm | exact SBM]. intros a Ha. exfalso. exact (Ha eq_refl).
  Qed.

  (* [comment removed for export] *)
  Definition bc_st (st : ast) (c : Z) (fm : bool) : ast :=
    op_carve SBEG (if fm then add_meter (op_famap st c) 0 [(sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)), sh_lo (fa_beg SBEG c + r_mapped_fa (a_reg st c)) + KFAMAP / 8)] 0 else st) c.

  Definition pf_ret (sp ra s0v s1v s2v s3v s4v s5v s6v tp gp : word) (res : Z) (r : bvmap 5 word) : Prop :=
    getr r 10 = Z_to_bv 64 res /\ getr r 2 = sp /\ getr r 1 = ra
    /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 4 = tp /\ getr r 3 = gp.

  (* [comment removed for export] *)
  Definition ftest (st : ast) (c : Z) : Prop :=
    r_mapped_fa (a_reg st c) < 4 * (Z.of_nat (length (r_free (a_reg st c))) + carve_n (a_reg st c) c).

  Theorem popBC_katwD :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v s6v tp gp : word) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    a_cinit st = true -> a_kact st <= KCAP ->
    let r := a_reg st c in let au := r_alloc_user r in let mu := r_mapped_user r in let nf := Z.of_nat (length (r_free r)) in let mfa := r_mapped_fa r in
    let newn := carve_n r c in let tot := nf + newn in let lo := fa_beg SBEG c + mfa in
    a_cache st c = [] -> nf < cache_hint c -> au + csize c <= mu ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (fa_beg SBEG c <= z < lo)                                   (* [comment removed for export] *)
                      /\ (mfa + KFAMAP <= 2 ^ 29 -> ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8))) ->
    pf_regs sp (reginfo bt c) SBEG c regs -> getr regs 1 = Z_to_bv 64 0x519d8 -> getr regs 10 = Z_to_bv 64 0x10ab58 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (SBEG + c * 2 ^ 32) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 9 = Z_to_bv 64 tot -> getr regs 19 = Z_to_bv 64 newn -> getr regs 20 = Z_to_bv 64 (mu - au) -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP ->
    (CEIL + 512 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
        rdn BSEGS M (at_ sp k) 8 = Some (LE8 v)) ->
    writableZ BSEGS M (U sp - 512) (U sp - 64) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st c) ->
        WF bt (bc_st st c fm) Lc FF -> RepX bt (XL c) (bc_st st c fm) Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 512 <= U a < U sp - 64) \/ (fa_beg SBEG c <= U a < lo)
             \/ (mfa + KFAMAP <= 2 ^ 29 /\ ((lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)))
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 16 <= U a < reginfo bt c + 128)) /\ M' a <> None) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 1 r' ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ (st' = op_fhole st c /\ ftest st c)) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 512 <= U a < U sp - 64) /\ M' a <> None) \/ (mfa + KFAMAP <= 2 ^ 29 /\ lo <= U a < lo + KFAMAP)) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 0 r' ->
        katD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using N3FH N3F PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v tp gp Qok Qf Hc W RX HALT MW CINIT KC r au mu nf mfa newn tot lo HC0 NFH AUMU XOFF
           HR H1 H10 H11 H12 H13 H9 H19 H20 H4 H3 Etp Hsp Hret SLOTS WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    assert (ROOMF : mfa < 4 * tot -> mfa + KFAMAP <= 2 ^ 29) by (intros TST; exact (famap_room bt st Lc FF c _ _ W Hc TST)).
    destruct HR as (R2 & R8 & R18 & R21).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mu au nf mfa in E2, E3, E4, E6, E7, E8, E13, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & Y2 & Y3 & Y4 & _). fold r mu au in Y1a, Y1b, Y2, Y3, Y4.
    pose proof (csize_pos c Hc) as [CS1 CS2].
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    unfold KSPACE, PG, KUSERMAP, KFAMAP, KREGION_EXHAUST in *.
    set (RIz := reginfo bt c) in *.
    assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    assert (EFAB : fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384) by ((lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (LOB : SBEG <= lo /\ lo + 2 ^ 18 <= SBEG + 2 ^ 37) by ((lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end); rewrite EFAB; lia).
    assert (ENEW : (mu - au) / csize c = newn) by reflexivity.
    assert (N0 : 0 <= newn) by (rewrite <- ENEW; apply Z.div_pos; lia).
    assert (N1 : newn * csize c <= mu - au) by (rewrite <- ENEW; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (N2 : 4 * newn <= 2 ^ 18) by (clear - N0 N1 CS1 Y1b Y1a; nia).
    assert (TOT : 0 <= tot /\ 4 * tot <= mfa + 2 ^ 18 /\ 4 * tot <= 2 ^ 29 + 2 ^ 18) by ((lazymatch goal with |- ?G => let G' := eval unfold tot in G in change_no_check G' end); lia).
    (* [comment removed for export] *)
    assert (FAQF : mfa < 4 * tot -> mfa <= 4 * (mu / csize c)).
    { intros TST. apply (AsAinvRoom3.famap_fa_le mfa tot mu (csize c)); [clear - CS1; lia | clear - TOT; lia | exact TST | exact (AsAinvRoom3.fa_q_pop bt st Lc FF c _ _ W Hc)]. }
    set (spE := at_ sp (-64)).
    assert (UspE : U spE = U sp - 64) by ((lazymatch goal with |- ?G => let G' := eval unfold spE in G in change_no_check G' end); rewrite at_u by lia; lia).
    assert (RETE : ret_ok (Z_to_bv 64 0x519d8)) by (apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    assert (TAIL : forall (fm : bool) (M2 : mem) mdl2 (r2 : bvmap 5 word),
              WF bt (if fm then add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + 2 ^ 18 / 8)] 0 else st) Lc FF ->
              RepX bt (XL c) (if fm then add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + 2 ^ 18 / 8)] 0 else st) Lc FF M2 mdl2 ->
              (if fm then mfa + 2 ^ 18 <= 2 ^ 29 else 4 * tot <= mfa) ->
              same_except_vm mdl mdl2 -> lazy_kept IA Lc FF mdl mdl2 -> BackingAlgebra.model_ivs_wf mdl2 -> m_halted mdl2 = None ->
              (forall a : word, M2 a <> M a ->
                  ((U sp - 512 <= U a < U sp - 64) \/ (mfa + 2 ^ 18 <= 2 ^ 29 /\ ((lo <= U a < lo + 2 ^ 18) \/ (sh_lo lo <= U a < sh_lo lo + 2 ^ 18 / 8)))
                   \/ (T + 2872 <= U a < T + 2888) \/ (RIz + 24 <= U a < RIz + 32)) /\ M2 a <> None) ->
              getr r2 10 = Z_to_bv 64 1 -> getr r2 2 = spE -> getr r2 8 = Z_to_bv 64 RIz -> getr r2 9 = Z_to_bv 64 tot -> getr r2 18 = Z_to_bv 64 (SBEG + c * 2 ^ 32) ->
              getr r2 19 = Z_to_bv 64 newn -> getr r2 20 = Z_to_bv 64 (mu - au) -> getr r2 21 = Z_to_bv 64 (csize c) -> getr r2 4 = tp -> getr r2 3 = gp ->
              katwD BSEGS (mkCfg (mkst r2 (Z_to_bv 64 0x519d8) M2 rom) mdl2) Qok Qf).
    { intros fm M2 mdl2 r2 W2 RX2 ENOUGH SEV2 LK2 MW2 HL2 FOOT2 A10 A2 A8 A9 A18 A19 A20 A21 A4 A3.
      set (st2 := if fm then add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + 2 ^ 18 / 8)] 0 else st) in *.
      assert (EREG : r_alloc_user (a_reg st2 c) = au /\ r_mapped_user (a_reg st2 c) = mu /\ r_free (a_reg st2 c) = r_free r
                     /\ r_mapped_fa (a_reg st2 c) = (if fm then mfa + 2 ^ 18 else mfa) /\ a_cinit st2 = true).
      { (lazymatch goal with |- ?G => let G' := eval unfold st2 in G in change_no_check G' end). destruct fm; [| repeat split; [reflexivity .. | exact CINIT]].
        destruct (famap_fields st c c) as (F1 & F2 & F3 & F4 & _). rewrite Z.eqb_refl in F3. unfold KFAMAP in F3.
        (lazymatch goal with |- ?G => let G' := eval cbn [add_meter a_reg a_cinit] in G in change_no_check G' end). repeat split; [exact F2 | exact F1 | exact F4 | exact F3 | exact CINIT]. }
      destruct EREG as (EAU & EMU & EFR & EFA & ECI).
      replace (Z_to_bv 64 0x519d8 : word) with (0x519d8%bv : word) by (apply bv_eq; reflexivity).
      assert (SL2 : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
                rdn BSEGS M2 (at_ sp k) 8 = Some (LE8 v)).
      { intros k v Hin. rewrite <- (SLOTS k v Hin).
        assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        destruct (decide (M2 x = M x)) as [E | NE]; [exact E|]. exfalso. destruct (FOOT2 x NE) as [F _].
        pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _).
        pose proof (pk_thread_geom2 bt st Lc FF W) as (_&_&_&_&_&_&S3'). unfold AS_HEAPLO in S3'.
        assert (QQ : lo + 2 ^ 18 <= CEIL) by (clear - LOB S2; lia).
        destruct (sh_band lo (2 ^ 18) ltac:((lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia) ltac:(lia) QQ ltac:(reflexivity)) as (_ & _ & SHB2). unfold sh_lo in F.
        replace (2 ^ 18 / 8) with (2 ^ 15) in * by reflexivity. clear - F Hx K SP1 CR T2 SHB2 ERI E10 S2 LOB. lia. }
      apply (popC_katwD bt BT_segs BT_ia X c st2 Lc FF M2 rom mdl2 r2 sp ra s0v s1v s2v s3v s4v s5v s6v Qok Qf Hc W2 RX2 HL2 ECI).
      - intros z Hz. destruct (XOFF z Hz) as (X1 & _ & _ & X4 & X5). split; [exact X1|]. rewrite EFA. intros Hin. fold mfa lo in X4, X5.
        destruct fm; [| apply X4; (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end); lia].
        destruct (Z_lt_le_dec z lo) as [L | L]; [apply X4; unfold lo in *; lia | apply (proj1 (X5 ENOUGH)); unfold lo in *; lia].
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EAU, EMU. exact AUMU.
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EFR, EFA. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite EAU, EMU. rewrite ENEW. fold nf. destruct fm; [unfold tot in TOT; lia | unfold tot in ENOUGH; exact ENOUGH].
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). apply (carve_room bt st2 Lc FF c _ _ W2 Hc); [ | rewrite EFR; exact NFH | lia].
        (lazymatch goal with |- ?G => let G' := eval unfold st2 in G in change_no_check G' end). destruct fm; [| exact HC0].
        change (a_cache (add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + 2 ^ 18 / 8)] 0)) with (a_cache (op_famap st c)).
        rewrite (proj1 (proj2 (famap_rest st c))). exact HC0.
      - (lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end). fold RIz. repeat split; assumption.
      - exact A10.
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EFR. (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite EAU, EMU, ENEW. exact A9.
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold carve_n in G in change_no_check G' end). rewrite EAU, EMU, ENEW. exact A19.
      - (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EAU, EMU. exact A20.
      - split; lia.
      - exact Hret.
      - exact (SL2 (-8) ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)). - exact (SL2 (-16) s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)). - exact (SL2 (-24) s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)).
      - exact (SL2 (-32) s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)). - exact (SL2 (-40) s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)). - exact (SL2 (-48) s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)).
      - exact (SL2 (-56) s5v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)). - exact (SL2 (-64) s6v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10)).
      - intros r' M' mdl' W3 RX3 SBM3 FOOT3 POST3.
        cbv zeta in FOOT3. rewrite EFR in FOOT3. unfold carve_n in FOOT3. rewrite EAU, EMU, ENEW in FOOT3. fold nf RIz in FOOT3.
        destruct POST3 as (P10 & P2 & P1 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & PAG).
        assert (NFT : fm = false -> ~ ftest st c) by (intros Efm; rewrite Efm in ENOUGH; (lazymatch goal with |- ?G => let G' := eval unfold ftest in G in change_no_check G' end); change (~ mfa < 4 * tot); lia).
        apply (CONT1 fm r' M' mdl' NFT); [exact W3 | exact RX3 | | | | | | ].
        + eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
        + intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl' SBM3 a Ha). exact (LK2 a Ha).
        + exact (model_ivs_wf_sbm mdl2 mdl' SBM3 MW2).
        + exact (halted_sbm mdl2 mdl' SBM3 HL2).
        + intros a Ha. destruct (decide (M' a = M2 a)) as [E | NE].
          * rewrite E in Ha |- *. destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. fold RIz. replace (2 ^ 18 / 8) with (2 ^ 15) in * by reflexivity. unfold lo in *. clear - F E7. lia.
          * destruct (FOOT3 a NE) as [F Dd]. split; [| exact Dd]. fold RIz. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). unfold tot in TOT, ENOUGH. destruct fm; clear - F TOT E7 N0 ENOUGH; lia.
        + (lazymatch goal with |- ?G => let G' := eval unfold pf_ret in G in change_no_check G' end). repeat (split; [assumption|]).
          split; [rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact A4 | rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact A3]. }
    (* [comment removed for export] *)
    destruct (Z_le_gt_dec (4 * tot) mfa) as [ENO | NEED].
    - apply (popBe_katwD bt BT_segs BT_ia X c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x519d8) (Z_to_bv 64 RIz) (Z_to_bv 64 tot) (Z_to_bv 64 (SBEG + c * 2 ^ 32)) (Z_to_bv 64 newn)
               tot Qok Qf Hc W RX HALT ltac:(intros z Hz; exact (proj1 (XOFF z Hz))) H1 R2 H11 H13 R8 H9 R18 H19 ltac:(rewrite UspE; lia) RETE ltac:(lia) ENO).
      + intros i Hi. rewrite UspE in Hi. apply WSTK. lia.
      + intros r2 M2 mdl2 RX2 SBM2 MI2 FOOT2 (P10 & P2 & P1 & P8 & P9 & P18 & P19 & PAG).
        apply (TAIL false M2 mdl2 r2 W RX2 ENO (same_but_materialized_except_vm _ _ SBM2) (lazy_kept_sbm bt Lc FF mdl mdl2 SBM2) (model_ivs_wf_sbm mdl mdl2 SBM2 MW) (halted_sbm mdl mdl2 SBM2 HALT));
          [ | exact P10 | exact P2 | exact P8 | exact P9 | exact P18 | exact P19 | | | | ].
        * intros a Ha. destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. left. rewrite UspE in F. lia.
        * rewrite (PAG 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H20.
        * rewrite (PAG 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact R21.
        * rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4.
        * rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3.
    - destruct (r_fhole (a_reg st c)) eqn:FH.
      { apply (popBf_katwD_h bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3FH c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x519d8)
               (Z_to_bv 64 RIz) (Z_to_bv 64 tot) (Z_to_bv 64 (SBEG + c * 2 ^ 32)) (Z_to_bv 64 newn) (Z_to_bv 64 (mu - au)) (Z_to_bv 64 (csize c)) tp gp tot Qok Qf
               Hc W RX HALT MW FH ltac:(fold r mfa; (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); apply ROOMF; lia) ltac:(apply FAQF; lia) KC).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & X5). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
        assert (RMx : mfa + 2 ^ 18 <= 2 ^ 29) by (apply ROOMF; lia). destruct (X5 RMx) as [X5a X5b]. repeat split; assumption.
      + exact H1. + exact R2. + exact H4. + exact H3. + exact Etp. + exact H10. + exact H11. + exact H12. + exact H13. + exact R8. + exact H9. + exact R18. + exact H19. + exact H20. + exact R21.
      + rewrite UspE. lia.
      + exact RETE.
      + lia.
      + fold r mfa. lia.
      + intros i Hi. rewrite UspE in Hi. apply WSTK. lia.
      + intros r2 M2 mdl2. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). intros W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 P10 P2 P1 P8 P9 P18 P19 P20 P21 P4 P3.
        assert (RM : mfa + 2 ^ 18 <= 2 ^ 29) by (apply ROOMF; lia).
        apply (TAIL true M2 mdl2 r2 W2 RX2 RM SEV2 LK2 MW2 HL2); [ | exact P10 | exact P2 | exact P8 | exact P9 | exact P18 | exact P19 | exact P20 | exact P21 | exact P4 | exact P3].
        intros a Ha. destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. rewrite UspE in F. fold RIz in F. clear - F RM. lia.
      + intros r0 r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 AG POST2. fold r mfa lo in FOOT2. unfold KFAMAP in FOOT2.
        destruct POST2 as (P10 & P2 & P1 & P8 & P9 & P18 & P19 & PAG).
        assert (SL2 : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
                  rdn BSEGS M2 (at_ sp k) 8 = Some (LE8 v)).
        { intros k v Hin. rewrite <- (SLOTS k v Hin).
          assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
          apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
          destruct (decide (M2 x = M x)) as [E | NE]; [exact E|]. exfalso. destruct (FOOT2 x NE) as [[F _] | F]; [rewrite UspE in F; lia|].
          clear - F Hx K SP1 CR S2 LOB. lia. }
        replace (Z_to_bv 64 0x519d8 : word) with (0x519d8%bv : word) by (apply bv_eq; reflexivity).
        apply (popF_katD (XL c) st2 Lc FF M2 rom mdl2 r2 sp ra s0v s1v s2v s3v s4v s5v s6v Qf W2 RX2 HL2 P2 P10 Hret ltac:(split; lia) SL2).
        intros r3 mdl3 RX3 SBM3 MI3 (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & QAG).
        apply (CONT0 r3 M2 mdl3 st2 ltac:(destruct EST as [E | E]; [left; exact E | right; split; [exact E | (lazymatch goal with |- ?G => let G' := eval unfold ftest in G in change_no_check G' end); change (mfa < 4 * tot); lia]]) W2 RX3).
        * eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
        * intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
        * exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
        * exact (halted_sbm mdl2 mdl3 SBM3 HL2).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). destruct (FOOT2 a Ha) as [[F Dd] | F]; [left; split; [rewrite UspE in F; lia | exact Dd] | right; split; [apply ROOMF; lia | exact F]].
        * (lazymatch goal with |- ?G => let G' := eval unfold pf_ret in G in change_no_check G' end). repeat (split; [assumption|]).
          split.
          -- rewrite (QAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4.
          -- rewrite (QAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3. }
      { apply (popBf_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x519d8)
               (Z_to_bv 64 RIz) (Z_to_bv 64 tot) (Z_to_bv 64 (SBEG + c * 2 ^ 32)) (Z_to_bv 64 newn) (Z_to_bv 64 (mu - au)) (Z_to_bv 64 (csize c)) tp gp tot Qok Qf
               Hc W RX HALT MW FH ltac:(fold r mfa; (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end); apply ROOMF; lia) ltac:(apply FAQF; lia) KC).
      + intros z Hz. destruct (XOFF z Hz) as (X1 & X2 & X3 & X4 & X5). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end).
        assert (RMx : mfa + 2 ^ 18 <= 2 ^ 29) by (apply ROOMF; lia). destruct (X5 RMx) as [X5a X5b]. repeat split; assumption.
      + exact H1. + exact R2. + exact H4. + exact H3. + exact Etp. + exact H10. + exact H11. + exact H12. + exact H13. + exact R8. + exact H9. + exact R18. + exact H19. + exact H20. + exact R21.
      + rewrite UspE. lia.
      + exact RETE.
      + lia.
      + fold r mfa. lia.
      + intros i Hi. rewrite UspE in Hi. apply WSTK. lia.
      + intros r2 M2 mdl2. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). intros W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 P10 P2 P1 P8 P9 P18 P19 P20 P21 P4 P3.
        assert (RM : mfa + 2 ^ 18 <= 2 ^ 29) by (apply ROOMF; lia).
        apply (TAIL true M2 mdl2 r2 W2 RX2 RM SEV2 LK2 MW2 HL2); [ | exact P10 | exact P2 | exact P8 | exact P9 | exact P18 | exact P19 | exact P20 | exact P21 | exact P4 | exact P3].
        intros a Ha. destruct (FOOT2 a Ha) as [F Dd]. split; [| exact Dd]. rewrite UspE in F. fold RIz in F. clear - F RM. lia.
      + intros r0 r2 M2 mdl2 st2 EST W2 RX2 SEV2 LK2 MW2 HL2 FOOT2 AG POST2. fold r mfa lo in FOOT2. unfold KFAMAP in FOOT2.
        destruct POST2 as (P10 & P2 & P1 & P8 & P9 & P18 & P19 & PAG).
        assert (SL2 : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
                  rdn BSEGS M2 (at_ sp k) 8 = Some (LE8 v)).
        { intros k v Hin. rewrite <- (SLOTS k v Hin).
          assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
          apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
          destruct (decide (M2 x = M x)) as [E | NE]; [exact E|]. exfalso. destruct (FOOT2 x NE) as [[F _] | F]; [rewrite UspE in F; lia|].
          clear - F Hx K SP1 CR S2 LOB. lia. }
        replace (Z_to_bv 64 0x519d8 : word) with (0x519d8%bv : word) by (apply bv_eq; reflexivity).
        apply (popF_katD (XL c) st2 Lc FF M2 rom mdl2 r2 sp ra s0v s1v s2v s3v s4v s5v s6v Qf W2 RX2 HL2 P2 P10 Hret ltac:(split; lia) SL2).
        intros r3 mdl3 RX3 SBM3 MI3 (Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & QAG).
        apply (CONT0 r3 M2 mdl3 st2 ltac:(destruct EST as [E | E]; [left; exact E | right; split; [exact E | (lazymatch goal with |- ?G => let G' := eval unfold ftest in G in change_no_check G' end); change (mfa < 4 * tot); lia]]) W2 RX3).
        * eapply same_except_vm_trans; [exact SEV2 | apply same_but_materialized_except_vm; exact SBM3].
        * intros a Ha. rewrite (lazy_kept_sbm bt Lc FF mdl2 mdl3 SBM3 a Ha). exact (LK2 a Ha).
        * exact (model_ivs_wf_sbm mdl2 mdl3 SBM3 MW2).
        * exact (halted_sbm mdl2 mdl3 SBM3 HL2).
        * intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). destruct (FOOT2 a Ha) as [[F Dd] | F]; [left; split; [rewrite UspE in F; lia | exact Dd] | right; split; [apply ROOMF; lia | exact F]].
        * (lazymatch goal with |- ?G => let G' := eval unfold pf_ret in G in change_no_check G' end). repeat (split; [assumption|]).
          split.
          -- rewrite (QAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (PAG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4.
          -- rewrite (QAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (PAG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3. }
  Qed.
End L3.
End WithCeil.
