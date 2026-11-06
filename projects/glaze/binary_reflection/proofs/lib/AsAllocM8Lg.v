(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8pb.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp.
Import OSSVerify.glaze.binary_reflection.images.Asan.
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

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.



Section FPGen.
Context {fx : FPState}.
Section PFNOMAP.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments ASEGS Hd.
  Hypothesis WX : wx_segs_nowrap ASEGS.

  Theorem pf_nomap_katwD :
    forall (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
           (sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp : word) (RIz SPB c req au mu nf : Z) (Qok Qf : config -> Prop),
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 RIz -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47) -> 1 <= c <= 30 -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000) -> au + csize c * req <= mu -> 0 <= nf <= 2 ^ 27 ->
    (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64) -> (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64) ->
    store_ok ASEGS mem (at_ sp (-64)) 64 = true ->
    rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 SPB)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)) ->
    rdn ASEGS mem (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)) ->
    hid_off Hd (0x103f18 + 32) 8 -> hid_off Hd RIz 128 -> hid_off Hd (U sp - 64) 64 ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall (r : bvmap 5 word) mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        pf_regs sp RIz SPB c r -> getr r 1 = Z_to_bv 64 0x50f68 ->
        getr r 10 = Z_to_bv 64 0x103f18 -> getr r 11 = Z_to_bv 64 RIz -> getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32) ->
        getr r 13 = Z_to_bv 64 (nf + (mu - au) / csize c) ->
        getr r 9 = Z_to_bv 64 (nf + (mu - au) / csize c) -> getr r 19 = Z_to_bv 64 ((mu - au) / csize c) ->
        getr r 20 = Z_to_bv 64 (mu - au) -> getr r 4 = tp -> getr r 3 = gp ->
        katwD ASEGS (mkCfg (mkst r (0x4ea98 : word) (pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v) rom) mdlm) Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50dd4 : word) mem rom) model) Qok Qf.
  Proof using WX HOFFSEG.
    intros A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp RIz SPB c req au mu nf Qok Qf
           H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hc Hreq Hau Hno Hnf HSPB HRI Hstk C_sbeg R_au R_mu R_nf
           HDsbeg HDRI HDf HALT LC AWF MI CONT.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hau as [[AU0 AU1] AU2].
    set (M0 := pf_m0 mem sp ra s0v s1v s2v s3v s4v s5v s6v).
    assert (CELLR : forall (cc : Z) (k : nat) v, 0 <= cc -> cc + Z.of_nat k < 2 ^ 64 -> hid_off Hd cc (Z.of_nat k) ->
               rdn ASEGS mem (Z_to_bv 64 cc) k = Some v -> rdn ASEGS (mrestrict Hd mem) (Z_to_bv 64 cc) k = Some v).
    { intros cc k v Hc0 Hc1 Hh Hr. rewrite rdn_mrestrict; [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hh]. }
    destruct (pf_head_nomap (mrestrict Hd mem) rom sp ra s0v s1v s2v s3v s4v s5v s6v stats RIz SPB c req au mu regs
                H1 H2 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 (conj SP1 SP2) Hc Hreq (conj (conj AU0 AU1) AU2) HSPB (conj RI1 RI2)
                ltac:(rewrite store_ok_mrestrict; [exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDf | lia | lia]])
                (CELLR (0x103f18 + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) HDsbeg C_sbeg)
                (CELLR (RIz + 32) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(eapply hid_off_sub; [exact HDRI | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]) R_au)
                (CELLR (RIz + 48) 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) ltac:(eapply hid_off_sub; [exact HDRI | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]) R_mu) Hno)
      as (r1 & RUN1 & PR1 & A10 & A13 & A20 & AG1).
    rewrite pf_m0_mrestrict in RUN1 by (first [lia | exact HDf]). fold M0 in RUN1.
    assert (M0out : forall x : word, (U x < U sp - 64 \/ U sp <= U x) -> M0 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M0 in G in change_no_check G' end); apply pf_m0_outside; [lia | exact Hx]).
    assert (Rnf0 : rdn ASEGS (mrestrict Hd M0) (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { rewrite rdn_mrestrict; [ | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); eapply hid_off_sub; [exact HDRI | lia | lia]].
      rewrite <- R_nf. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply M0out. lia. }
    destruct (pf_efs_call (mrestrict Hd M0) rom sp RIz SPB c au mu nf r1 PR1 A10 A13 A20 (conj SP1 SP2) Hc ltac:(lia) Hnf (conj RI1 RI2) Rnf0)
      as (r2 & RUN2 & PR2 & B1 & B10 & B11 & B12 & B13 & B9 & B19 & B20 & AG2).
    apply (lift_katwD_mem Hd HOFFSEG WX A regs (0x50dd4 : word) r2 (0x4ea98 : word) mem M0 rom model Qok Qf
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
End AsAllocM8pb.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Lb.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp AsAllocM8pb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La.
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
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
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
    writableZ ASEGS M (U sp - 48) (U sp) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> (U sp - 48 <= U a < U sp) /\ M' a <> None) ->
        efs_post sp ra s0v s1v s2v s3v 1 regs r' ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x4ea98%bv : word) M rom) mdl) Qok Qf.
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
    In (0x103f38, 8%nat, SBEG) (bt_consts bt) ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI)) ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 0x103f18 -> getr regs 11 = stats -> getr regs 12 = Z_to_bv 64 c ->
    getr regs 13 = Z_to_bv 64 (reginfo bt c) -> getr regs 14 = Z_to_bv 64 req ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    (CEIL + 64 <= U sp /\ U sp + 16 <= 2 ^ 47) -> (1 <= req /\ csize c * req <= 2 ^ 18) ->
    r_alloc_user r + csize c * req <= r_mapped_user r ->
    writableZ ASEGS M (U sp - 64) (U sp) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> (U sp - 64 <= U a < U sp) /\ M' a <> None) ->
        (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
            rdn ASEGS M' (at_ sp k) 8 = Some (LE8 v)) ->
        pf_regs sp (reginfo bt c) SBEG c r' -> getr r' 1 = Z_to_bv 64 0x50f68 ->
        getr r' 10 = Z_to_bv 64 0x103f18 -> getr r' 11 = Z_to_bv 64 (reginfo bt c) -> getr r' 12 = Z_to_bv 64 (SBEG + c * 2 ^ 32) ->
        getr r' 13 = Z_to_bv 64 (nf + carve_n r c) -> getr r' 9 = Z_to_bv 64 (nf + carve_n r c) -> getr r' 19 = Z_to_bv 64 (carve_n r c) ->
        getr r' 20 = Z_to_bv 64 (r_mapped_user r - r_alloc_user r) -> getr r' 4 = tp -> getr r' 3 = gp ->
        katwD ASEGS (mkCfg (mkst r' (0x4ea98%bv : word) M' rom) mdl') Qok Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x50dd4%bv : word) M rom) mdl) Qok Qf.
  Proof using BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp req Qok Qf Hc W RX HALT CSBEG XOFF r nf
           H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 Hsp Hreq NOMAP WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold nf in E7.
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as ((Y1a & Y1b) & Y2 & Y3 & _). fold r in Y1a, Y1b, Y2, Y3.
    pose proof (img_lits bt st Lc FF W) as [I1 I2]. rewrite BT_ia in I1, I2. cbn [ia_img_lo ia_img_hi asan_addrs] in I1, I2.
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
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (HOFF : forall lo n, 0 <= lo -> lo + n < 2 ^ 64 -> (forall z, lo <= z < lo + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo n).
    { intros lo n L0 L1 Hz x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    assert (RDRI : forall k v, 8 <= k -> k + 8 <= 128 -> rdn ASEGS M0 (Z_to_bv 64 (RIz + k)) 8 = Some v -> rdn ASEGS M (Z_to_bv 64 (RIz + k)) 8 = Some v).
    { intros k v K0 K1 Hr. apply (repx_rd (XL c) M M0 D (RIz + k) 8 v); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact Hr]. }
    apply (pf_nomap_katwD Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v s6v stats tp gp
             RIz SBEG c req (r_alloc_user r) (r_mapped_user r) nf Qok Qf
             H1 H2 H4 H3 H10 H11 H12 H13 H14 H8 H9 H18 H19 H20 H21 H22 ltac:(lia) Hc Hreq ltac:(lia) NOMAP ltac:(lia) ltac:(lia) ltac:(lia)).
    - apply (writableZ_sok M (U sp - 64) (U sp)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (repx_rd (XL c) M M0 D (0x103f18 + 32) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XIM; cbn in Hi; lia | exact KSB].
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
End AsAllocM8Lb.
Require Stdlib.Sorting.Permutation LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Le.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvRoom3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lch.
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
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
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
        rdn ASEGS M (at_ sp k) 8 = Some (LE8 v)) ->
    (forall (r' : bvmap 5 word) mdl', RepX bt Y st Lc FF M mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        pf_post0 sp ra s0v s1v s2v s3v s4v s5v s6v regs r' -> katD ASEGS (mkCfg (mkst r' ra M rom) mdl') Q) ->
    katD ASEGS (mkCfg (mkst regs (0x50f68%bv : word) M rom) mdl) Q.
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
    pf_regs sp (reginfo bt c) SBEG c regs -> getr regs 1 = Z_to_bv 64 0x50f68 -> getr regs 10 = Z_to_bv 64 0x103f18 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (SBEG + c * 2 ^ 32) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 9 = Z_to_bv 64 tot -> getr regs 19 = Z_to_bv 64 newn -> getr regs 20 = Z_to_bv 64 (mu - au) -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP ->
    (CEIL + 512 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra ->
    (forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
        rdn ASEGS M (at_ sp k) 8 = Some (LE8 v)) ->
    writableZ ASEGS M (U sp - 512) (U sp - 64) ->
    (forall (fm : bool) (r' : bvmap 5 word) (M' : mem) mdl',
        (fm = false -> ~ ftest st c) ->
        WF bt (bc_st st c fm) Lc FF -> RepX bt (XL c) (bc_st st c fm) Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 512 <= U a < U sp - 64) \/ (fa_beg SBEG c <= U a < lo)
             \/ (mfa + KFAMAP <= 2 ^ 29 /\ ((lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)))
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 16 <= U a < reginfo bt c + 128)) /\ M' a <> None) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 1 r' ->
        katwD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ (st' = op_fhole st c /\ ftest st c)) ->
        WF bt st' Lc FF -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 512 <= U a < U sp - 64) /\ M' a <> None) \/ (mfa + KFAMAP <= 2 ^ 29 /\ lo <= U a < lo + KFAMAP)) ->
        pf_ret sp ra s0v s1v s2v s3v s4v s5v s6v tp gp 0 r' ->
        katD ASEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD ASEGS (mkCfg (mkst regs (0x4ea98%bv : word) M rom) mdl) Qok Qf.
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
    assert (RETE : ret_ok (Z_to_bv 64 0x50f68)) by (apply ret_ok_lit; [lia | reflexivity]).
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
              katwD ASEGS (mkCfg (mkst r2 (Z_to_bv 64 0x50f68) M2 rom) mdl2) Qok Qf).
    { intros fm M2 mdl2 r2 W2 RX2 ENOUGH SEV2 LK2 MW2 HL2 FOOT2 A10 A2 A8 A9 A18 A19 A20 A21 A4 A3.
      set (st2 := if fm then add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + 2 ^ 18 / 8)] 0 else st) in *.
      assert (EREG : r_alloc_user (a_reg st2 c) = au /\ r_mapped_user (a_reg st2 c) = mu /\ r_free (a_reg st2 c) = r_free r
                     /\ r_mapped_fa (a_reg st2 c) = (if fm then mfa + 2 ^ 18 else mfa) /\ a_cinit st2 = true).
      { (lazymatch goal with |- ?G => let G' := eval unfold st2 in G in change_no_check G' end). destruct fm; [| repeat split; [reflexivity .. | exact CINIT]].
        destruct (famap_fields st c c) as (F1 & F2 & F3 & F4 & _). rewrite Z.eqb_refl in F3. unfold KFAMAP in F3.
        (lazymatch goal with |- ?G => let G' := eval cbn [add_meter a_reg a_cinit] in G in change_no_check G' end). repeat split; [exact F2 | exact F1 | exact F4 | exact F3 | exact CINIT]. }
      destruct EREG as (EAU & EMU & EFR & EFA & ECI).
      replace (Z_to_bv 64 0x50f68 : word) with (0x50f68%bv : word) by (apply bv_eq; reflexivity).
      assert (SL2 : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v)] ->
                rdn ASEGS M2 (at_ sp k) 8 = Some (LE8 v)).
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
    - apply (popBe_katwD bt BT_segs BT_ia X c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x50f68) (Z_to_bv 64 RIz) (Z_to_bv 64 tot) (Z_to_bv 64 (SBEG + c * 2 ^ 32)) (Z_to_bv 64 newn)
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
      { apply (popBf_katwD_h bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3FH c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x50f68)
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
                  rdn ASEGS M2 (at_ sp k) 8 = Some (LE8 v)).
        { intros k v Hin. rewrite <- (SLOTS k v Hin).
          assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
          apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
          destruct (decide (M2 x = M x)) as [E | NE]; [exact E|]. exfalso. destruct (FOOT2 x NE) as [[F _] | F]; [rewrite UspE in F; lia|].
          clear - F Hx K SP1 CR S2 LOB. lia. }
        replace (Z_to_bv 64 0x50f68 : word) with (0x50f68%bv : word) by (apply bv_eq; reflexivity).
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
      { apply (popBf_katwD bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS PCELLS X N3F c st Lc FF M rom mdl regs spE (Z_to_bv 64 0x50f68)
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
                  rdn ASEGS M2 (at_ sp k) 8 = Some (LE8 v)).
        { intros k v Hin. rewrite <- (SLOTS k v Hin).
          assert (K : -64 <= k <= -8) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
          apply rdn_ext; [rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
          destruct (decide (M2 x = M x)) as [E | NE]; [exact E|]. exfalso. destruct (FOOT2 x NE) as [[F _] | F]; [rewrite UspE in F; lia|].
          clear - F Hx K SP1 CR S2 LOB. lia. }
        replace (Z_to_bv 64 0x50f68 : word) with (0x50f68%bv : word) by (apply bv_eq; reflexivity).
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
End AsAllocM8Le.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8n.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RF0.
  Variables (M rom : word -> option byte) (sp ra s0v s1v : word).          (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Lemma rf_ret0 :
    exists r, msteps ASEGS (mkst regs (0x50a0c : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9]) regs r.
  Proof using S_s1 S_s0 S_ra Hret H10 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_50a04 D_50a04 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_50a0c D_50a0c ra S_ra.                    (* [comment removed for export] *)
      cld8 F_50a10 D_50a10 s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50a14 D_50a14 s1v S_s1.                   (* [comment removed for export] *)
      an F_50a18 D_50a18.                              (* [comment removed for export] *)
      aret F_50a1c D_50a1c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End RF0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CB0.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4v : word).   (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 8.                            (* [comment removed for export] *)
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis S_ra : rdn ASEGS M (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS M (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS M (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS M (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS M (at_ sp (-40)) 8 = Some (LE8 s3v).
  Hypothesis S_s4 : rdn ASEGS M (at_ sp (-48)) 8 = Some (LE8 s4v).
  Lemma cb_ret0 :
    exists r, msteps ASEGS (mkst regs (0x5052c : word) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 11; 13; 18; 19; 20]) regs r.
  Proof using S_s4 S_s3 S_s2 S_s1 S_s0 S_ra Hret H18 H10 H2.
    pose proof (u64_range sp) as Hspr.
    wd_eexists. split.
    - ab_tk F_50524 D_50524 ltac:(condz).              (* [comment removed for export] *)
      an F_5053c D_5053c.                              (* [comment removed for export] *)
      an F_50540 D_50540.                              (* [comment removed for export] *)
      ab_ft F_50544 D_50544 ltac:(condz).              (* [comment removed for export] *)
      an F_50548 D_50548.                              (* [comment removed for export] *)
      cld8 F_50478 D_50478 ra S_ra.                    (* [comment removed for export] *)
      cld8 F_5047c D_5047c s0v S_s0.                   (* [comment removed for export] *)
      cld8 F_50480 D_50480 s1v S_s1.                   (* [comment removed for export] *)
      cld8 F_50484 D_50484 s2v S_s2.                   (* [comment removed for export] *)
      cld8 F_50488 D_50488 s3v S_s3.                   (* [comment removed for export] *)
      cld8 F_5048c D_5048c s4v S_s4.                   (* [comment removed for export] *)
      an F_50490 D_50490.                              (* [comment removed for export] *)
      aret F_50494 D_50494 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End CB0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition am_null_mem (M : word -> option byte) (sp tp : word) : word -> option byte :=
  wbytes (wbytes (wbytes M (Z_to_bv 64 0x1897e0) [Z_to_bv 8 1]) (at_ sp 120) (LE8 (Z_to_bv 64 0x4bb10))) (at_ tp (-164)) (LE4 12).

Section AMNULL.
  Variables (M rom : word -> option byte) (sp tp rai s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v s0' : word).
  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 160 <= 2 ^ 47)%Z.
  Hypothesis Htp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  Hypothesis Hret : ret_ok rai.
  Hypothesis C_mrn : rdn ASEGS M (Z_to_bv 64 0x1897e1) 1 = Some [Z_to_bv 8 1].
  Hypothesis SOK_oom : store_ok ASEGS M (Z_to_bv 64 0x1897e0) 1 = true.
  Hypothesis SOK_err : store_ok ASEGS M (at_ tp (-164)) 4 = true.
  Hypothesis SOK_stk : store_ok ASEGS M (at_ sp 120) 8 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(120, Z_to_bv 64 0x4baf4); (112, s0v); (104, s1v); (96, s2v); (88, s3v); (80, s4v); (72, s5v); (64, s6v); (56, s7v); (48, s8v);
               (40, s9v); (32, s10v); (24, s11v); (136, rai); (128, s0')]%Z -> rdn ASEGS M (at_ sp k) 8 = Some (LE8 v).

  Ltac sld F D vv k :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := LE8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi, ?at_at; fold_at_vars; rewrite ?at_addi, ?at_at; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold am_null_mem in G in change_no_check G' end);
          repeat (rewrite wc_rdn_wbytes_out3; [ | rd8_side ]);
          first [apply (SL k vv) | replace (at_ sp _) with (at_ sp k) by (f_equal; lia); apply (SL k vv)]; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  Lemma am_null :
    exists r, msteps ASEGS (mkst regs (0x4bdc4 : word) M rom) (mkst r rai (am_null_mem M sp tp) rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 2 = at_ sp 144 /\ getr r 1 = rai
      /\ getr r 8 = s0' /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ getr r 26 = s10v /\ getr r 27 = s11v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) regs r.
  Proof using SL SOK_stk SOK_err SOK_oom C_mrn Hret Htp Hsp H10 H4 H2 s0v.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range tp) as Htpr. destruct Htp as [TP1 TP2].
    wd_eexists. split.
    - an F_4bdbc D_4bdbc.                              (* [comment removed for export] *)
      ab_tk F_4bdc0 D_4bdc0 ltac:(condz).              (* [comment removed for export] *)
      an F_4be8c D_4be8c.                              (* [comment removed for export] *)
      an F_7a934 D_7a934.                              (* [comment removed for export] *)
      an F_7a938 D_7a938.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 0x1897e0) (b := Z_to_bv 8 1);
          [exact F_7a93c | reflexivity | exact D_7a93c
          | gres; rwH; apply bv_eq; vm_compute; reflexivity
          | gres; rwH; reflexivity
          | apply bv_eq; vm_compute; reflexivity
          | exact SOK_oom ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      rt F_7a940 D_7a940.                              (* [comment removed for export] *)
      an F_4be90 D_4be90.                              (* [comment removed for export] *)
      an F_7a944 D_7a944.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lb with (b := Z_to_bv 8 1);
          [exact F_7a948 | reflexivity | exact D_7a948
          | gres; rwH;
            lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 0x1897e1 : word) by (apply bv_eq; vm_compute; reflexivity) end;
            rewrite rdn_wbytes_out; [exact C_mrn | rd8_side | rd8_side | rd8_side ] ]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      an F_7a94c D_7a94c.                              (* [comment removed for export] *)
      rt F_7a950 D_7a950.                              (* [comment removed for export] *)
      ab_tk F_4be94 D_4be94 ltac:(first [condz | vm_compute; reflexivity]).   (* [comment removed for export] *)
      an F_4c36c D_4c36c.                              (* [comment removed for export] *)
      an F_4c370 D_4c370.                              (* [comment removed for export] *)
      an F_4c250 D_4c250.                              (* [comment removed for export] *)
      sld F_4c254 D_4c254 (Z_to_bv 64 0x4baf4) 120%Z.  (* [comment removed for export] *)
      sld F_4c258 D_4c258 s0v 112%Z. sld F_4c25c D_4c25c s1v 104%Z. sld F_4c260 D_4c260 s2v 96%Z. sld F_4c264 D_4c264 s3v 88%Z.
      sld F_4c268 D_4c268 s4v 80%Z. sld F_4c26c D_4c26c s5v 72%Z. sld F_4c270 D_4c270 s6v 64%Z. sld F_4c274 D_4c274 s7v 56%Z.
      sld F_4c278 D_4c278 s8v 48%Z. sld F_4c27c D_4c27c s9v 40%Z. sld F_4c280 D_4c280 s10v 32%Z. sld F_4c284 D_4c284 s11v 24%Z.
      an F_4c288 D_4c288.                              (* [comment removed for export] *)
      rt F_4c28c D_4c28c.                              (* [comment removed for export] *)
      ab_tk F_4baec D_4baec ltac:(condz).              (* [comment removed for export] *)
      an F_4bb00 D_4bb00.                              (* [comment removed for export] *)
      an F_4bb04 D_4bb04.                              (* [comment removed for export] *)
      an F_88810 D_88810.                              (* [comment removed for export] *)
      fsd F_88814 D_88814 (at_ sp 120).                (* [comment removed for export] *)
      an F_88818 D_88818.                              (* [comment removed for export] *)
      an F_e6d14 D_e6d14.                              (* [comment removed for export] *)
      an F_e6d18 D_e6d18.                              (* [comment removed for export] *)
      rt F_e6d1c D_e6d1c.                              (* [comment removed for export] *)
      an F_8881c D_8881c.                              (* [comment removed for export] *)
      fsw F_88820 D_88820 (at_ tp (-164)).             (* [comment removed for export] *)
      fld F_88824 D_88824 (Z_to_bv 64 0x4bb10).        (* [comment removed for export] *)
      an F_88828 D_88828.                              (* [comment removed for export] *)
      rt F_8882c D_8882c.                              (* [comment removed for export] *)
      an F_4bb08 D_4bb08.                              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes M _ _) _ _) _ _) with (am_null_mem M sp tp).
      sld F_4bb0c D_4bb0c rai 136%Z.                   (* [comment removed for export] *)
      sld F_4bb10 D_4bb10 s0' 128%Z.                   (* [comment removed for export] *)
      an F_4bb14 D_4bb14.                              (* [comment removed for export] *)
      aret F_4bb18 D_4bb18 rai.                        (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End AMNULL.
End FPGen.
End AsAllocM8n.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMRunN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA AsAllocM8n.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_litN : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_litN : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_litN. exact Hc. Qed.

Section RUNN.
  Variables (M4 rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = at_ sp2 (-48).
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 0.
  Hypothesis H18 : getr r0 18 = Z_to_bv 64 8.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M4 (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn ASEGS M4 (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn ASEGS M4 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS M4 (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn ASEGS M4 (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_mrn : rdn ASEGS M4 (Z_to_bv 64 0x1897e1) 1 = Some [Z_to_bv 8 1].           (* [comment removed for export] *)
  Hypothesis SOK_oom : store_ok ASEGS M4 (Z_to_bv 64 0x1897e0) 1 = true.
  Hypothesis SOK_err : store_ok ASEGS M4 (at_ tp (-164)) 4 = true.
  (* [comment removed for export] *)
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 1); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (needed n)); (-48, Z_to_bv 64 (rz n))]%Z ->
    rdn ASEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis FA : forall (k : Z) (v : word),
    In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
    rdn ASEGS M4 (at_ S k) 8 = Some (LE8 v).
  Hypothesis FI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn ASEGS M4 (at_ S k) 8 = Some (LE8 v).

  Definition mn_mem : word -> option byte := am_null_mem M4 sp2 tp.

  Lemma mn_mem_outside : forall x : word,
    (U x <> 0x1897e0)%Z -> (U x < U S - 2152 \/ U S - 2144 <= U x)%Z -> (U x < U tp - 164 \/ U tp - 160 <= U x)%Z -> mn_mem x = M4 x.
  Proof using Gtp GS.
    intros x X1 X2 X3. pose proof (u64_range S). pose proof (u64_range tp). destruct GS as (G1 & G2 & _). destruct Gtp as [P1 P2].
    (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; rewrite ?u_Z2bv by lia;
      (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma mn_mem_errno : forall x : word, (U tp - 164 <= U x < U tp - 160)%Z -> mn_mem x <> None.
  Proof using Gtp.
    intros x Hx. pose proof (u64_range tp). destruct Gtp as [P1 P2]. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma mn_mem_grows : mem_grows M4 mn_mem.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Theorem run_mA_null :
    exists (r : bvmap 5 word),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x5052c) M4 rom) (mkst r (getr R 1) mn_mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using FI FA FC SOK_err SOK_oom C_mrn C_mcs C_fum C_gcf C_inited Hstk Gtp GT Gn GS Hret H18 H10 H3 H4 H2 x19 x18 n T.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Usp2 : U sp2 = (U S - 2272)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RETC : ret_ok (at_ ARB 0x4bdc4)) by (rewrite (ARB_litN 0x4bdc4) by lia; apply ret_ok_lit; [lia | reflexivity]).
    assert (RETI : ret_ok (at_ ARB 0x6e600)) by (rewrite (ARB_litN 0x6e600) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    destruct (cb_ret0 M4 rom sp2 (at_ ARB 0x4bdc4) (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (needed n)) (Z_to_bv 64 (rz n)) r0
                H2 H10 H18 RETC
                (FC (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto))
                (FC (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)) (FC (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)))
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & AG1).
    replace (0x5052c : word) with (Z_to_bv 64 0x5052c : word) in RUN1 by (apply bv_eq; reflexivity).
    rewrite (ARB_litN 0x4bdc4) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (SLs : forall (k : Z) (v : word),
              In (k, v) [(120, Z_to_bv 64 0x4baf4); (112, S); (104, Z_to_bv 64 n); (96, x18); (88, x19); (80, at_ S (-2128)); (72, at_ S (-81));
                         (64, getr R 22); (56, getr R 23); (48, getr R 24); (40, getr R 25); (32, getr R 26); (24, getr R 27);
                         (136, at_ ARB 0x6e600); (128, S)]%Z -> rdn ASEGS M4 (at_ sp2 k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite at_at.
      assert (EK : In ((-2272 + k)%Z, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27))).
      { (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). rewrite (ARB_litN 0x4baf4) by lia. cbn [In] in Hin |- *.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); tauto|]). destruct Hin. }
      exact (FA _ _ EK). }
    destruct (am_null M4 rom sp2 tp (at_ ARB 0x6e600) S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S r1
                A2 ltac:(rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4)
                A10 ltac:(rewrite Usp2; lia) ltac:(split; lia) RETI C_mrn SOK_oom SOK_err
                ltac:(eapply (store_ok_sub ASEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                SLs)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    replace (0x4bdc4 : word) with (Z_to_bv 64 0x4bdc4 : word) in RUN2 by (apply bv_eq; reflexivity).
    fold mn_mem in RUN2.
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in B2.
    (* [comment removed for export] *)
    assert (MH : mpH ASEGS asan_mp_tab M4 S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x1990a8) 34) with (Z_to_bv 64 0x1990ca : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub ASEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (FIn : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS mn_mem (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (FI k v Hin).
      assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply mn_mem_outside; lia. }
    destruct (mp_epi ASEGS asan_mp_tab asan_mp_tab_ok R M4 rom (getr R 1) S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) mn_mem r2 B2 FIn)
      as (r3 & RUN3 & C10 & C1 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & CK).
    cbn [mt_rb asan_mp_tab] in RUN3. rewrite (ARB_litN 0x6e600) in RUN3 by lia. rewrite (ARB_litN 0x6e600) in RUN2 by lia.
    exists r3. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
    assert (NI : forall i : reg, In i [3; 4; 22; 23; 24; 25; 26; 27] -> ~ In i [1; 2; 8; 9; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split; [rewrite C10; exact B10|]. split; [exact C1|]. split; [exact C2|].
    split. { rewrite (CK 3%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3. }
    split. { rewrite (CK 4%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4. }
    split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|]. split; [exact C20|]. split; [exact C21|].
    split; [rewrite (CK 22%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B22|]. split; [rewrite (CK 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B23|].
    split; [rewrite (CK 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B24|]. split; [rewrite (CK 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B25|].
    split; [rewrite (CK 26%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B26|]. rewrite (CK 27%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact B27.
  Qed.
End RUNN.
End FPGen.
End AsAllocMRunN.
Module AsAllocMRunNs.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9d.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_litNs : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_litNs : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_litNs. exact Hc. Qed.

Section RUNNS.
  Variables (M4 rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis HL : la_regs (at_ S (-2320)) (Z_to_bv 64 0x1041c8) (sec_needed n) r0.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 0.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (64513 <= n <= 2 ^ 34)%Z.
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.
  Hypothesis Gtp : (AIMGLO + 164 <= U tp /\ U tp <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M4 (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn ASEGS M4 (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn ASEGS M4 (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS M4 (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn ASEGS M4 (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_mrn : rdn ASEGS M4 (Z_to_bv 64 0x1897e1) 1 = Some [Z_to_bv 8 1].           (* [comment removed for export] *)
  Hypothesis SOK_oom : store_ok ASEGS M4 (Z_to_bv 64 0x1897e0) 1 = true.
  Hypothesis SOK_err : store_ok ASEGS M4 (at_ tp (-164)) 4 = true.
  (* [comment removed for export] *)
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, at_ ARB 0x4bdc4); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
    rdn ASEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  (* [comment removed for export] *)
  Hypothesis FLA : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50324); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x103f18); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
    rdn ASEGS M4 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v).
  Hypothesis FA : forall (k : Z) (v : word),
    In (k, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
    rdn ASEGS M4 (at_ S k) 8 = Some (LE8 v).
  Hypothesis FI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn ASEGS M4 (at_ S k) 8 = Some (LE8 v).

  Definition mn_mem : word -> option byte := am_null_mem M4 sp2 tp.

  Lemma mn_mem_outside : forall x : word,
    (U x <> 0x1897e0)%Z -> (U x < U S - 2152 \/ U S - 2144 <= U x)%Z -> (U x < U tp - 164 \/ U tp - 160 <= U x)%Z -> mn_mem x = M4 x.
  Proof using Gtp GS.
    intros x X1 X2 X3. pose proof (u64_range S). pose proof (u64_range tp). destruct GS as (G1 & G2 & _). destruct Gtp as [P1 P2].
    (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; rewrite ?u_Z2bv by lia;
      (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma mn_mem_errno : forall x : word, (U tp - 164 <= U x < U tp - 160)%Z -> mn_mem x <> None.
  Proof using Gtp.
    intros x Hx. pose proof (u64_range tp). destruct Gtp as [P1 P2]. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end).
    rewrite wbytes_inside; [discriminate | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
  Qed.
  Lemma mn_mem_grows : mem_grows M4 mn_mem.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold mn_mem, am_null_mem in G in change_no_check G' end). do 3 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Theorem run_mS_null :
    exists (r : bvmap 5 word),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x50610) M4 rom) (mkst r (getr R 1) mn_mem rom)
      /\ getr r 10 = Z_to_bv 64 0 /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using FI FA FLA FC SOK_err SOK_oom C_mrn C_mcs C_fum C_gcf C_inited Hstk Gtp GT Gn GS Hret H10 H3 H4 HL x19 x18 n T.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Usp2 : U sp2 = (U S - 2272)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (RETC : ret_ok (at_ ARB 0x4bdc4)) by (rewrite (ARB_litNs 0x4bdc4) by lia; apply ret_ok_lit; [lia | reflexivity]).
    assert (RETI : ret_ok (at_ ARB 0x6e600)) by (rewrite (ARB_litNs 0x6e600) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    assert (RETL : ret_ok (Z_to_bv 64 0x50324)) by (apply ret_ok_lit; [lia | reflexivity]).
    destruct (la_fail M4 rom (at_ S (-2320)) (Z_to_bv 64 0x50324) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (Z_to_bv 64 n) (Z_to_bv 64 0x103f18) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7) (Z_to_bv 64 0x1041c8) (sec_needed n) r0
                HL RETL H10
                (FLA (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-56)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-64)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-72)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FLA (-80)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FLA (-88)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)))
      as (r0' & RUN0 & (L10 & L2 & L1 & L8 & L9 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & AG0)).
    replace (0x50610 : word) with (Z_to_bv 64 0x50610 : word) in RUN0 by (apply bv_eq; reflexivity).
    assert (K0 : forall i : reg, In i [3; 4; 26; 27] -> getr r0' i = getr r0 i).
    { intros i Hi. apply AG0. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (cbs_ret M4 rom sp2 (at_ ARB 0x4bdc4) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048) (Z_to_bv 64 0) r0'
                ltac:(rewrite L2; rewrite !at_at; reflexivity) L8 L10 RETC
                (FC (-8)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-16)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-24)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20))
                (FC (-32)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-40)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)) (FC (-48)%Z _ ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20)))
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & AG1).
    replace (0x50324 : word) with (Z_to_bv 64 0x50324 : word) in RUN1 by (apply bv_eq; reflexivity).
    rewrite (ARB_litNs 0x4bdc4) in RUN1 by lia.
    assert (H4' : getr r0' 4 = tp) by (rewrite K0 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H4).
    assert (H3' : getr r0' 3 = getr R 3) by (rewrite K0 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H3).
    (* [comment removed for export] *)
    assert (SLs : forall (k : Z) (v : word),
              In (k, v) [(120, Z_to_bv 64 0x4baf4); (112, S); (104, Z_to_bv 64 n); (96, x18); (88, x19); (80, at_ S (-2128)); (72, at_ S (-81));
                         (64, getr R 22); (56, getr R 23); (48, getr R 24); (40, getr R 25); (32, getr R 26); (24, getr R 27);
                         (136, at_ ARB 0x6e600); (128, S)]%Z -> rdn ASEGS M4 (at_ sp2 k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite at_at.
      assert (EK : In ((-2272 + k)%Z, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27))).
      { (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). rewrite (ARB_litNs 0x4baf4) by lia. cbn [In] in Hin |- *.
        repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); tauto|]). destruct Hin. }
      exact (FA _ _ EK). }
    destruct (am_null M4 rom sp2 tp (at_ ARB 0x6e600) S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S r1
                A2 ltac:(rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi); exact H4')
                A10 ltac:(rewrite Usp2; lia) ltac:(split; lia) RETI C_mrn SOK_oom SOK_err
                ltac:(eapply (store_ok_sub ASEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                SLs)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    replace (0x4bdc4 : word) with (Z_to_bv 64 0x4bdc4 : word) in RUN2 by (apply bv_eq; reflexivity).
    fold mn_mem in RUN2.
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in B2.
    (* [comment removed for export] *)
    assert (MH : mpH ASEGS asan_mp_tab M4 S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x1990a8) 34) with (Z_to_bv 64 0x1990ca : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub ASEGS M4 (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (FIn : forall (k : Z) (v : word),
              In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn ASEGS mn_mem (at_ S k) 8 = Some (LE8 v)).
    { intros k v Hin. rewrite <- (FI k v Hin).
      assert (Hk : (-56 <= k /\ k + 8 <= 0)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply mn_mem_outside; lia. }
    destruct (mp_epi ASEGS asan_mp_tab asan_mp_tab_ok R M4 rom (getr R 1) S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) mn_mem r2 B2 FIn)
      as (r3 & RUN3 & C10 & C1 & C2 & C8 & C9 & C18 & C19 & C20 & C21 & CK).
    cbn [mt_rb asan_mp_tab] in RUN3. rewrite (ARB_litNs 0x6e600) in RUN3 by lia. rewrite (ARB_litNs 0x6e600) in RUN2 by lia.
    exists r3. split.
    { eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3]. }
    assert (NI : forall i : reg, In i [3; 4; 22; 23; 24; 25; 26; 27] -> ~ In i [1; 2; 8; 9; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split; [rewrite C10; exact B10|]. split; [exact C1|]. split; [exact C2|].
    split. { rewrite (CK 3%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H3'. }
    split. { rewrite (CK 4%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi).
             rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). exact H4'. }
    split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|]. split; [exact C20|]. split; [exact C21|].
    split; [rewrite (CK 22%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B22|]. split; [rewrite (CK 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B23|].
    split; [rewrite (CK 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B24|]. split; [rewrite (CK 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B25|].
    split; [rewrite (CK 26%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B26|]. rewrite (CK 27%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact B27.
  Qed.
End RUNNS.
End FPGen.
End AsAllocMRunNs.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld AsAllocM8Le.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | hs_am_lia ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).





Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma mod8_of_64k : forall x, x mod 2 ^ 16 = 0 -> x mod 8 = 0.
Proof. intros x Hx. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition liftable (K : config -> Prop) : Prop :=
  forall (Hd : word -> bool), H_off_segments ASEGS Hd -> wx_segs_nowrap ASEGS ->
  forall (A : list (Z * Z)) regs (pc : word) r (pc' : word) (M M' rom : mem) (model : Model),
    msteps ASEGS (mkst regs pc (mrestrict Hd M) rom) (mkst r pc' (mrestrict Hd M') rom) ->
    (forall a : word, Hd a = true -> M' a = M a) ->
    m_halted model = None -> lazy_cover Hd (m_vm_lazy model) A -> A_wf A -> MInv A model ->
    (forall mdlm, same_but_materialized model mdlm -> MInv A mdlm -> K (mkCfg (mkst r pc' M' rom) mdlm)) ->
    K (mkCfg (mkst regs pc M rom) model).
(* [comment removed for export] *)
Definition s_regs (r : bvmap 5 word) (g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) : Prop :=
  getr r 18 = g2 /\ getr r 19 = g3 /\ getr r 20 = g4 /\ getr r 21 = g5 /\ getr r 22 = g6 /\ getr r 23 = g7 /\ getr r 24 = g8 /\ getr r 25 = g9
  /\ getr r 26 = g10 /\ getr r 27 = g11.

(* [comment removed for export] *)
Lemma refill_cache_ne : forall (st : ast) (c m : Z), 1 <= m <= Z.of_nat (length (r_free (a_reg st c))) -> a_cache (op_refill st c m) c <> [].
Proof using.
  intros st c m Hm E. unfold op_refill, set_cache in E. cbn in E. unfold fupdZ in E. rewrite Z.eqb_refl in E.
  apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn [length] in E. lia.
Qed.

Lemma liftable_katD : forall Q, liftable (fun cf => katD ASEGS cf Q).
Proof using. intros Q Hd HO WX A regs pc r pc' M M' rom model. apply (lift_katD_mem Hd HO WX). Qed.
Lemma liftable_katwD : forall Qok Qf, liftable (fun cf => katwD ASEGS cf Qok Qf).
Proof using. intros Qok Qf Hd HO WX A regs pc r pc' M M' rom model. apply (lift_katwD_mem Hd HO WX). Qed.
Lemma liftable_katsD : forall Qok Qf, liftable (fun cf => katsD ASEGS cf Qok Qf).
Proof using.
  intros Qok Qf Hd HO WX A regs pc r pc' M M' rom model RUN SAME HALT LC AWF MI CONT.
  apply (katsD_msteps_acct ASEGS Hd HO WX A (mkst regs pc M rom) (mkst r pc' (mrestrict Hd M') rom) model Qok Qf LC AWF MI HALT).
  { rewrite mk_restrict_mkst. exact RUN. }
  intros mdlm MIm SBMm HC1. rewrite mk_unrestrict_mkst.
  replace (RiscvSemantics.ms_mem (mkst regs pc M rom)) with M by reflexivity.
  rewrite (mk_munrestrict_same Hd M M' SAME). exact (CONT mdlm SBMm MIm).
Qed.

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
  Lemma repx_widen_step : forall (Y Z0 : Z -> Prop) (Zd : Xdec Z0) st Lc FF (M M' : mem) mdl mdl',
    WF bt st Lc FF -> RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> (Z0 (U a) \/ ~ rep_cells bt st Lc FF (U a)) /\ M' a <> None) ->
    (forall a : word, Z0 (U a) -> M' a <> None) ->
    MInv (a_aa st) mdl' -> same_but_materialized mdl mdl' ->
    RepX bt (fun z => Y z \/ Z0 z) st Lc FF M' mdl'.
  Proof using.
    intros Y Z0 Zd st Lc FF M M' mdl mdl' W (M0 & R & D) CH ZDEF MI SBM.
    set (M0' := fun a : word => if Zd (U a) then M0 a else if decide (M a = M0 a) then M' a else M0 a).
    exists M0'. split.
    - apply (Rep_sbm bt st Lc FF M0' mdl mdl'); [| exact MI | exact SBM].
      apply (Rep_frame bt st Lc FF M0 M0' mdl W R). intros a Ha. unfold M0' in Ha |- *.
      destruct (Zd (U a)) as [HZ | NZ]; [exfalso; exact (Ha eq_refl)|].
      destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
      rewrite <- E in Ha. destruct (CH a Ha) as [[F | F] Dd]; [exfalso; exact (NZ F) | exact (conj F Dd)].
    - intros a Ha. unfold M0' in Ha.
      destruct (Zd (U a)) as [HZ | NZ]; [split; [right; exact HZ | exact (ZDEF a HZ)]|].
      destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl)|].
      destruct (D a NE) as [HY Dd]. split; [left; exact HY|].
      destruct (decide (M' a = M a)) as [E2 | NE2]; [rewrite E2; exact Dd | exact (proj2 (CH a NE2))].
  Qed.

  (* [comment removed for export] *)
  Definition gf_inv (M : mem) (c : Z) (spR raR s0R s1R g_ra g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : word) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (reginfo bt c)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 60)))
    /\ (forall (k : Z) (v : word),
          In (k, v) [(-8, g_ra); (-16, g0); (-24, g1); (-32, g2); (-40, g3); (-48, g4); (-56, g5); (-64, g6); (-72, g7); (-80, g8); (-88, g9); (-96, g10); (-104, g11)] ->
          rdn ASEGS M (at_ (at_ spR (-32)) k) 8 = Some (LE8 v))
    /\ (forall (k : Z) (v : word), In (k, v) [(-8, raR); (-16, s0R); (-24, s1R)] -> rdn ASEGS M (at_ spR k) 8 = Some (LE8 v)).

  (* [comment removed for export] *)
  Lemma repx_step_widen : forall (Y Z0 FOOT : Z -> Prop) (Zd : Xdec Z0) st st' Lc Lc' FF FF' (M M' : mem) mdl mdl',
    RepX bt Y st Lc FF M mdl ->
    (forall a : word, M' a <> M a -> (Z0 (U a) \/ FOOT (U a)) /\ M' a <> None) ->
    (forall a : word, Z0 (U a) -> M' a <> None) ->
    (forall M0 M0' : mem, Rep bt st Lc FF M0 mdl ->
        (forall a : word, M a <> M0 a -> Y (U a) /\ M a <> None) ->
        (forall a : word, M0' a <> M0 a -> FOOT (U a) /\ ~ Z0 (U a) /\ M0' a <> None) ->
        (forall a : word, ~ Y (U a) -> ~ Z0 (U a) -> M0' a = M' a) ->
        (forall a : word, Z0 (U a) -> M0' a = M0 a) ->
        Rep bt st' Lc' FF' M0' mdl') ->
    RepX bt (fun z => Y z \/ Z0 z) st' Lc' FF' M' mdl'.
  Proof using.
    intros Y Z0 FOOT Zd st st' Lc Lc' FF FF' M M' mdl mdl' (M0 & R & D) CH ZDEF STEP.
    set (M0' := fun a : word => if Zd (U a) then M0 a else if decide (M a = M0 a) then M' a else M0 a).
    exists M0'. split.
    - apply (STEP M0 M0' R D).
      + intros a Ha. unfold M0' in Ha |- *. destruct (Zd (U a)) as [HZ | NZ]; [exfalso; exact (Ha eq_refl)|].
        destruct (decide (M a = M0 a)) as [E | NE]; [| exfalso; exact (Ha eq_refl)].
        rewrite <- E in Ha. destruct (CH a Ha) as [[F | F] Dd]; [exfalso; exact (NZ F) | exact (conj F (conj NZ Dd))].
      + intros a NY NZ. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Zd (U a)) as [HZ | _]; [exfalso; exact (NZ HZ)|].
        destruct (decide (M a = M0 a)) as [_ | NE]; [reflexivity | exfalso; exact (NY (proj1 (D a NE)))].
      + intros a HZ. (lazymatch goal with |- ?G => let G' := eval unfold M0' in G in change_no_check G' end). destruct (Zd (U a)) as [_ | NZ]; [reflexivity | exfalso; exact (NZ HZ)].
    - intros a Ha. unfold M0' in Ha.
      destruct (Zd (U a)) as [HZ | NZ]; [split; [right; exact HZ | exact (ZDEF a HZ)]|].
      destruct (decide (M a = M0 a)) as [E | NE]; [exfalso; exact (Ha eq_refl)|].
      destruct (D a NE) as [HY Dd]. split; [left; exact HY|].
      destruct (decide (M' a = M a)) as [E2 | NE2]; [rewrite E2; exact Dd | exact (proj2 (CH a NE2))].
  Qed.


  Theorem refill_head_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None ->
    a_cinit st = true -> a_cache st c = [] ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    nf < cache_hint c ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 (T + T_PC) -> getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) ->
    getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) ->
    writableZ ASEGS M (U spR - 160) (U spR) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        RepX bt (XL c) st Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (reginfo bt c <= U a < reginfo bt c + 8)) /\ M' a <> None) ->
        gf_inv M' c spR raR (getr regs 8) (getr regs 9) (Z_to_bv 64 0x50a0c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 (cache_hint c))
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ->
        gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c (cache_hint c) r' ->
        getr r' 1 = Z_to_bv 64 0x50d88 -> getr r' 10 = Z_to_bv 64 0x103f18 -> getr r' 11 = at_ (Z_to_bv 64 T) 2768 -> getr r' 12 = Z_to_bv 64 c ->
        getr r' 13 = Z_to_bv 64 (reginfo bt c) -> getr r' 14 = Z_to_bv 64 (cache_hint c - nf) -> getr r' 4 = tp -> getr r' 3 = gp ->
        K (mkCfg (mkst r' (0x50dd4%bv : word) M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl).
  Proof using PCELLS CELLS MIDEND FL PGP TSDP TP BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 r nf NF XOFF H1 H2 H4 H3 H10 H11 H12 H13 Hsp WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (CELL_sbeg & _).
    pose proof PCELLS as (_ & PC_rib & _).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & _). destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite CINIT in P2.
    destruct (R4 c Hc) as [(G0 & G8 & G16 & _ & _ & _ & _ & _ & _ & GW) _]. fold r nf in G16.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (h := cache_hint c) in *.
    assert (Hh : 1 <= h <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold h, cache_hint in G in change_no_check G' end); lia).
    assert (EMC : cache_max c = 2 * h) by reflexivity.
    assert (EMC2 : cache_max c / 2 = h) by (rewrite EMC, Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    (* [comment removed for export] *)
    assert (YIMG : forall z, X z -> ~ (AIMGLO <= z < AIMGHI)) by (intros z Hz; exact (proj1 (proj2 (XOFF z Hz)))).
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (XOFF i Hx)) Hi)).
    (* [comment removed for export] *)
    assert (KMC : rdn ASEGS M (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c)))
      by (apply (repx_rd X M M0 D _ 4 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; lia | exact P2]).
    assert (KSB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (KRIB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rib ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). unfold KSPACE in KRIB.
    assert (KMTX : rdn ASEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)))
      by (apply (repx_rd X M M0 D RIz 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G0]).
    assert (KNF : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)))
      by (apply (repx_rd X M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16]).
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr X M M0 D); [lia | lia | exact GW]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    set (cache := Z_to_bv 64 (T + 208) : word). set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word).
    assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (rf_pro ASEGS ARB asan_HRF regs Mr rom raR spR cache pc (Z_to_bv 64 0x103f18) c (cache_max c) H1 H2 H10 H11 H12 H13
                ltac:(rewrite EMC; split; [lia | rewrite Z.mul_comm; apply Z_mod_mult])
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia])
                ltac:(lia) ltac:(rewrite Ucache, Upc; lia)
                ltac:(replace (at_ pc 4) with (Z_to_bv 64 (T + 208 + 80 * c + 4)) by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; reflexivity);
                      apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHrt; cbn in Hi; lia | exact KMC]))
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & AG1).
    set (MR1 := rf_m1 regs Mr raR spR) in *.
    set (spG := at_ spR (-32)) in *.
    assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    assert (OUT1 : forall x : word, (U x < U spR - 32 \/ U spR <= U x) -> MR1 x = Mr x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end). apply (rf_m1_outside ARB regs Mr raR spR ltac:(lia) x Hx). }
    assert (RD1 : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k <= CEIL -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS MR1 (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. rewrite <- (RDM z k v Z0 ltac:(lia) Hh0 Hr). apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT1. lia. }
    assert (SBEG8 : SBEG mod 8 = 0).
    { pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). exact (mod8_of_64k _ S16). }
    assert (NI : forall i : reg, In i [18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 4%bv; 3%bv] -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Xi. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi|]). exact Hi. }
    destruct (gfp_pre MR1 rom spG (at_ ARB 0x50a0c) pc (Z_to_bv 64 (cache_max c / 2)) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (at_ cache 2560) (at_ pc 16) SBEG c (cache_max c / 2) nf r1
                A1 A2 A10 A11 A12 A13 A14 A8 A9
                (NI 18%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 19%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 20%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 21%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 22%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 23%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 24%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 25%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 26%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 27%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                ltac:(rewrite UspG; lia) Hc ltac:(rewrite EMC2; lia) ltac:(split; [lia | split; [lia | exact SBEG8]]) ltac:(rewrite UspG; lia))
      as (r2 & RUN2 & GR & B1 & B10 & B11 & B12 & B13 & B14 & AG2).
    - (* [comment removed for export] *) eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply rf_m1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia].
      apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KSB].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KRIB].
    - apply (RD1 RIz 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KMTX].
    - apply (RD1 (RIz + 16) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KNF].
    - eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply rf_m1_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia].
      apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (* [comment removed for export] *)
      rewrite EMC2 in *.
      set (M' := r1_mem M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                   (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz).
      assert (EMEM : gfp_m1 MR1 spG (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                       (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (SBEG + 2 ^ 37 + 128 * c) = mrestrict Hd M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite <- (r1_mem_mrestrict M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20)
                               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) Hd
                               ltac:(apply HOFF; intros z Hz; apply NHs; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia)).
        reflexivity. }
      rewrite EMEM in RUN2.
      rewrite (ARB_lit8 0x50acc) in RUN1 by lia. rewrite (ARB_lit8 0x509cc) in RUN1 by lia.
      replace (Z_to_bv 64 0x50acc : word) with (0x50acc%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x509cc : word) with (0x509cc%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
      + intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_outside; [lia | lia | | ].
        * pose proof (hid_true_off Hd a (U spR - 160) 160 Ha ltac:(apply HOFF; intros z Hz; apply NHs; lia)). lia.
        * pose proof (hid_true_off Hd a RIz 8 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
      + intros mdlm SBM MIm.
        assert (FOOTM : forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 8)) /\ M' a <> None).
        { intros a Ha.
          assert (IN : ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 8)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
          destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end); apply r1_mem_outside; [lia | lia | exact O1 | exact O2]].
          split; [exact IN|]. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_grows.
          destruct IN as [I1 | I2]; [destruct (WSTK (U a) I1) as [Dd _] | destruct (WRI (U a) ltac:(lia)) as [Dd _]]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
        destruct GR as (G2 & G8' & G9' & G18 & G19 & G20 & G21 & G22).
        apply (CONT r2 M' mdlm).
        * apply (repx_widen_step X (fun z => RIz <= z < RIz + 8) (Xdec_iv RIz (RIz + 8)) st Lc FF M M' mdl mdlm W RX); [ | | exact MIm | exact SBM].
          -- intros a Ha. destruct (FOOTM a Ha) as [[F | F] Dd]; (split; [| exact Dd]); [right | left; exact F].
             intros RCa. pose proof (rep_cells_lt_ceil bt BT_ia st Lc FF (U a) W RCa). lia.
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
        * exact SBM.
        * exact MIm.
        * exact FOOTM.
        * (lazymatch goal with |- ?G => let G' := eval unfold gf_inv in G in change_no_check G' end). fold RIz. split; [| split].
          -- (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_lock; lia.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_gslots; [lia | lia |]. rewrite (ARB_lit8 0x50a0c) by lia. exact Hin.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r1_mem_rslots; [lia | lia | exact Hin].
        * (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold RIz. rewrite ERI. unfold pc in G21. replace (at_ (Z_to_bv 64 (T + 208 + 80 * c)) 16) with (Z_to_bv 64 (T + 208 + 80 * c + 16)) in G21
            by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by lia; lia); rewrite !u_Z2bv by lia; reflexivity).
          repeat split; assumption.
        * exact B1.
        * exact B10.
        * rewrite B11. (lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end). apply bv_eq. rewrite !at_u by (rewrite ?u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. lia.
        * exact B12.
        * rewrite B13. rewrite ERI. reflexivity.
        * exact B14.
        * rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12). exact H4.
        * rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 13). exact H3.
  Qed.



  Theorem refill_head0_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR tp gp : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None ->
    a_cinit st = false -> a_cache st c = [] ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in
    nf < cache_hint c ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 4 = tp -> getr regs 3 = gp -> getr regs 10 = Z_to_bv 64 (T + T_PC) -> getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) ->
    getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) ->
    writableZ ASEGS M (U spR - 160) (U spR) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_cache_init st) Lc FF -> RepX bt (XL c) (op_cache_init st) Lc FF M' mdl' -> same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a -> ((U spR - 160 <= U a < U spR) \/ (reginfo bt c <= U a < reginfo bt c + 8) \/ (T + T_PC + 84 <= U a < T + T_PC + 2496)) /\ M' a <> None) ->
        gf_inv M' c spR raR (getr regs 8) (getr regs 9) (Z_to_bv 64 0x50a0c) (Z_to_bv 64 (T + T_PC + PC_SZ * c)) (Z_to_bv 64 (cache_hint c))
               (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ->
        gfp_regs (at_ spR (-32)) (Z_to_bv 64 (T + T_PC + PC_SZ * c + 16)) (reginfo bt c) SBEG c (cache_hint c) r' ->
        getr r' 1 = Z_to_bv 64 0x50d88 -> getr r' 10 = Z_to_bv 64 0x103f18 -> getr r' 11 = at_ (Z_to_bv 64 T) 2768 -> getr r' 12 = Z_to_bv 64 c ->
        getr r' 13 = Z_to_bv 64 (reginfo bt c) -> getr r' 14 = Z_to_bv 64 (cache_hint c - nf) -> getr r' 4 = tp -> getr r' 3 = gp ->
        K (mkCfg (mkst r' (0x50dd4%bv : word) M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl).
  Proof using PCELLS CELLS MIDEND FL PGP TSDP TP BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR tp gp Hc W RX HALT CINIT HC0 r nf NF XOFF H1 H2 H4 H3 H10 H11 H12 H13 Hsp WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
    pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (CELL_sbeg & _).
    pose proof PCELLS as (_ & PC_rib & _).
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15).
    pose proof R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & _). destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite CINIT in P2.
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _).
    destruct (R4 c Hc) as [(G0 & G8 & G16 & _ & _ & _ & _ & _ & _ & GW) _]. fold r nf in G16.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    set (h := cache_hint c) in *.
    assert (Hh : 1 <= h <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold h, cache_hint in G in change_no_check G' end); lia).
    assert (EMC : cache_max c = 2 * h) by reflexivity.
    assert (EMC2 : cache_max c / 2 = h) by (rewrite EMC, Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    (* [comment removed for export] *)
    assert (YIMG : forall z, X z -> ~ (AIMGLO <= z < AIMGHI)) by (intros z Hz; exact (proj1 (proj2 (XOFF z Hz)))).
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (XOFF i Hx)) Hi)).
    (* [comment removed for export] *)
    assert (KMC : rdn ASEGS M (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 0))
      by (apply (repx_rd X M M0 D _ 4 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; lia | exact P2]).
    assert (KSB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (KRIB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rib ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). unfold KSPACE in KRIB.
    assert (KMTX : rdn ASEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)))
      by (apply (repx_rd X M M0 D RIz 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G0]).
    assert (KNF : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)))
      by (apply (repx_rd X M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16]).
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr X M M0 D); [lia | lia | exact GW]).
    assert (WT : writableZ ASEGS M T (T + 4096)) by (apply (repx_wr X M M0 D); [lia | lia | exact TW]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    set (cache := Z_to_bv 64 (T + 208) : word). set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word).
    assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (icmc_cache_max c Hc) as [EIC _].
    destruct (rf_pro0 ASEGS ARB asan_HRF ARB_ok regs Mr rom raR spR cache pc (Z_to_bv 64 0x103f18) c H1 H2 H10 H11 H12 H13
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by lia; lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia])
                ltac:(lia) ltac:(rewrite Ucache, Upc; lia)
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); rewrite store_ok_mrestrict; [apply (writableZ_sok M T (T + 4096)); [exact WT | rewrite at_u by lia; rewrite Ucache; lia | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia]
                                                             | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u by lia; rewrite Ucache; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHrt; lia])
                ltac:(replace (at_ pc 4) with (Z_to_bv 64 (T + 208 + 80 * c + 4)) by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; reflexivity);
                      apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHrt; cbn in Hi; lia | exact KMC]))
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & AG1).
    rewrite EIC in A9, A14.
    set (MR1 := ic_mem regs Mr raR spR cache 31) in *.
    set (spG := at_ spR (-32)) in *.
    assert (UspG : U spG = U spR - 32) by ((lazymatch goal with |- ?G => let G' := eval unfold spG in G in change_no_check G' end); rewrite at_u by lia; lia).
    assert (OUT1 : forall x : word, (U x < U spR - 32 \/ U spR <= U x) -> (U x < T + 208 + 84 \/ T + 208 + 2496 <= U x) -> MR1 x = Mr x).
    { intros x Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end). rewrite ic_mem_outside_p by (rewrite ?Ucache; first [lia | intros i Hi; lia]). apply (rf_m1_outside ARB regs Mr raR spR ltac:(lia) x Hx). }
    assert (RD1 : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k <= CEIL -> (z + Z.of_nat k <= T \/ T + 4096 <= z) -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS MR1 (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 ZT Hh0 Hr. rewrite <- (RDM z k v Z0 ltac:(lia) Hh0 Hr). apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply OUT1; [lia | clear - Hx ZT; lia]. }
    assert (SBEG8 : SBEG mod 8 = 0).
    { pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16). exact (mod8_of_64k _ S16). }
    assert (NI : forall i : reg, In i [18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 4%bv; 3%bv] -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Xi. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi|]). exact Hi. }
    destruct (gfp_pre MR1 rom spG (at_ ARB 0x50a0c) pc (Z_to_bv 64 (cache_max c / 2)) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (at_ cache 2560) (at_ pc 16) SBEG c (cache_max c / 2) nf r1
                A1 A2 A10 A11 A12 A13 A14 A8 A9
                (NI 18%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 19%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 20%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 21%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 22%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 23%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 24%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 25%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                (NI 26%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12)) (NI 27%bv ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12))
                ltac:(rewrite UspG; lia) Hc ltac:(rewrite EMC2; lia) ltac:(split; [lia | split; [lia | exact SBEG8]]) ltac:(rewrite UspG; lia))
      as (r2 & RUN2 & GR & B1 & B10 & B11 & B12 & B13 & B14 & AG2).
    - (* [comment removed for export] *) eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply ic_mem_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                    | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHs; lia].
      apply (writableZ_sok M (U spR - 160) (U spR)); [exact WSTK | rewrite at_u by (rewrite UspG; lia); rewrite UspG; lia | rewrite at_u by (rewrite UspG; lia); rewrite UspG; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TIMG; lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KSB].
    - apply RD1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TIMG; lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KRIB].
    - apply (RD1 RIz 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TSP ERI Hc; lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KMTX].
    - apply (RD1 (RIz + 16) 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - TSP ERI Hc; lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KNF].
    - eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold MR1 in G in change_no_check G' end); apply ic_mem_grows|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); apply HOFF; intros z Hz; apply NHri; lia].
      apply (writableZ_sok M RIz (RIz + 128)); [exact WRI | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (* [comment removed for export] *)
      rewrite EMC2 in *.
      set (M' := r10_mem regs M spR raR cache (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                   (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz).
      assert (EMEM : gfp_m1 MR1 spG (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                       (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (SBEG + 2 ^ 37 + 128 * c) = mrestrict Hd M').
      { (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite <- (r10_mem_mrestrict regs M spR raR cache (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20)
                               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) ltac:(rewrite Ucache; lia) Hd
                               ltac:(apply HOFF; intros z Hz; apply NHs; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia) ltac:(rewrite Ucache; apply HOFF; intros z Hz; apply NHrt; lia)).
        reflexivity. }
      assert (OUTM : forall a : word, (U a < U spR - 160 \/ U spR <= U a) -> (U a < RIz \/ RIz + 8 <= U a) ->
                 (forall i : Z, 1 <= i <= 31 -> (U a < T + 208 + 80 * i + 4 \/ T + 208 + 80 * i + 16 <= U a)) -> M' a = M a).
      { intros a A1' A2' A3'. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_outside; [lia | lia | rewrite Ucache; lia | exact A1' | exact A2' | rewrite Ucache; exact A3']. }
      rewrite EMEM in RUN2.
      rewrite (ARB_lit8 0x50acc) in RUN1 by lia. rewrite (ARB_lit8 0x509cc) in RUN1 by lia.
      replace (Z_to_bv 64 0x50acc : word) with (0x50acc%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x509cc : word) with (0x509cc%bv : word) in RUN1 by (apply bv_eq; reflexivity).
      apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl (msteps_trans _ _ _ _ RUN1 RUN2)); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
      + intros a Ha. apply OUTM.
        * pose proof (hid_true_off Hd a (U spR - 160) 160 Ha ltac:(apply HOFF; intros z Hz; apply NHs; lia)). lia.
        * pose proof (hid_true_off Hd a RIz 8 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
        * intros i Hi. pose proof (hid_true_off Hd a T 4096 Ha ltac:(apply HOFF; intros z Hz; apply NHrt; lia)). lia.
      + intros mdlm SBM MIm.
        assert (FOOTM : forall a : word, M' a <> M a ->
                  ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR) \/ (exists i, 1 <= i <= 31 /\ T + 208 + 80 * i + 4 <= U a < T + 208 + 80 * i + 16)) /\ M' a <> None).
        { intros a Ha.
          assert (DEF : (RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR) \/ (T <= U a < T + 4096) -> M' a <> None).
          { intros IN. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_grows.
            destruct IN as [I1 | [I2 | I3]]; [destruct (WRI (U a) ltac:(lia)) as [Dd _] | destruct (WSTK (U a) I2) as [Dd _] | destruct (WT (U a) I3) as [Dd _]]; rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
          destruct (Z_lt_le_dec (U a) (T + 208 + 84)) as [KK1|KK1].
          { assert (IN : ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
            destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; apply OUTM; [exact O1 | exact O2 | intros i Hi; lia]].
            split; [clear - IN; lia | apply DEF; clear - IN; lia]. }
          destruct (Z_lt_le_dec (U a) (T + 208 + 2496)) as [KK2|KK2].
          { (* [comment removed for export] *)
            set (i := (U a - (T + 208)) / 80). assert (Hi : 1 <= i <= 31 /\ T + 208 + 80 * i <= U a < T + 208 + 80 * i + 80).
            { (lazymatch goal with |- ?G => let G' := eval unfold i in G in change_no_check G' end). pose proof (Z.div_mod (U a - (T + 208)) 80 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (U a - (T + 208)) 80 ltac:(lia)) as MB.
              assert (1 <= (U a - (T + 208)) / 80) by (apply Z.div_le_lower_bound; lia). assert ((U a - (T + 208)) / 80 < 32) by (apply Z.div_lt_upper_bound; lia). lia. }
            destruct Hi as [Hi1 Hi2].
            destruct (Z_lt_le_dec (U a) (T + 208 + 80 * i + 4)) as [D1|D1]; [exfalso; apply Ha; apply OUTM; [clear - KK1 KK2 SP1 T2 CR; lia | clear - KK1 KK2 TSP ERI Hc; lia | intros j Hj; clear - D1 Hi2 Hj; nia]|].
            destruct (Z_lt_le_dec (U a) (T + 208 + 80 * i + 16)) as [D2|D2].
            - split; [right; right; exists i; split; [exact Hi1 | lia] | apply DEF; right; right; clear - KK1 KK2; lia].
            - exfalso. apply Ha. apply OUTM; [clear - KK2 SP1 T2 CR; lia | clear - KK1 KK2 TSP ERI Hc; lia | intros j Hj; clear - D2 Hi2 Hj; nia]. }
          assert (IN : ((RIz <= U a < RIz + 8) \/ (U spR - 160 <= U a < U spR)) \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 8 <= U a))) by (clear; lia).
          destruct IN as [IN | [O1 O2]]; [| exfalso; apply Ha; apply OUTM; [exact O1 | exact O2 | intros i Hi; lia]].
          split; [clear - IN; lia | apply DEF; clear - IN; lia]. }
        assert (W1 : WF bt (op_cache_init st) Lc FF) by (apply WF_cache_init; exact W).
        destruct GR as (G2 & G8' & G9' & G18 & G19 & G20 & G21 & G22).
        apply (CONT r2 M' mdlm).
        * exact W1.
        * apply (repx_step_widen X (fun z => RIz <= z < RIz + 8)
                   (fun z => (U spR - 160 <= z < U spR) \/ (exists i, 1 <= i <= 31 /\ T + 208 + 80 * i + 4 <= z < T + 208 + 80 * i + 16))
                   (Xdec_iv RIz (RIz + 8)) st (op_cache_init st) Lc Lc FF FF M M' mdl mdlm RX).
          -- intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. clear - F. tauto.
          -- intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_grows. destruct (WRI (U a) ltac:(lia)) as [Dd _]. rewrite Z_to_bv_bv_unsigned in Dd. exact Dd.
          -- intros N0 N0' RPn Dn DIFF EQ KEEP.
             apply (OPS_REP_cache_init_pf bt st Lc FF N0 N0' mdl mdlm W RPn); [ | | exact SBM | exact MIm].
             ++ intros a Ha. destruct (DIFF a Ha) as (F & _ & Dd). split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_cache_init, T_PC, PC_SZ in G in change_no_check G' end).
                destruct F as [F | (i & Hi & F)]; [right; lia | left; exists i; split; [exact Hi | lia]].
             ++ intros i Hi. destruct (icmc_cache_max i Hi) as [E1' E2'].
                destruct (r10_mem_cells ASEGS regs M spR raR cache (at_ ARB 0x50a0c) pc (Z_to_bv 64 h) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                            (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) ltac:(rewrite Ucache; lia) ltac:(rewrite Ucache; clear - TSP ERI Hc; lia) i ltac:(lia)) as [CM CS].
                fold M' in CM, CS. rewrite E1' in CM. rewrite E2' in CS.
                replace (at_ cache (80 * i + 4)) with (Z_to_bv 64 (T + 208 + 80 * i + 4)) in CM by (apply bv_eq; rewrite at_u by (rewrite Ucache; lia); rewrite Ucache, u_Z2bv by lia; lia).
                replace (at_ cache (80 * i + 8)) with (Z_to_bv 64 (T + 208 + 80 * i + 8)) in CS by (apply bv_eq; rewrite at_u by (rewrite Ucache; lia); rewrite Ucache, u_Z2bv by lia; lia).
                (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). rewrite ?BT_segs. split.
                ** rewrite <- CM. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
                   apply EQ; [apply XT; clear - Hx Hi; lia | clear - Hx Hi TSP ERI Hc; lia].
                ** rewrite <- CS. apply rdn_ext; [rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx.
                   apply EQ; [apply XT; clear - Hx Hi; lia | clear - Hx Hi TSP ERI Hc; lia].
        * exact SBM.
        * exact MIm.
        * intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. fold RIz.
          destruct F as [F | [F | (i & Hi & F)]]; [right; left; exact F | left; exact F | right; right; clear - F Hi; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold gf_inv in G in change_no_check G' end). fold RIz. split; [| split].
          -- (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_lock; lia.
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_gslots; first [rewrite (ARB_lit8 0x50a0c) by lia; exact Hin | rewrite ?Ucache; clear - TSP ERI Hc; lia | rewrite ?Ucache; lia].
          -- intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply r10_mem_rslots; first [exact Hin | rewrite ?Ucache; clear - TSP ERI Hc; lia | rewrite ?Ucache; lia].
        * (lazymatch goal with |- ?G => let G' := eval unfold gfp_regs in G in change_no_check G' end). fold RIz. rewrite ERI. unfold pc in G21. replace (at_ (Z_to_bv 64 (T + 208 + 80 * c)) 16) with (Z_to_bv 64 (T + 208 + 80 * c + 16)) in G21
            by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by lia; lia); rewrite !u_Z2bv by lia; reflexivity).
          repeat split; assumption.
        * exact B1.
        * exact B10.
        * rewrite B11. (lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end). apply bv_eq. rewrite !at_u by (rewrite ?u_Z2bv by lia; lia). rewrite !u_Z2bv by lia. lia.
        * exact B12.
        * rewrite B13. rewrite ERI. reflexivity.
        * exact B14.
        * rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12). exact H4.
        * rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi). rewrite (NI 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 13). exact H3.
  Qed.


End L3.
End WithCeil.
