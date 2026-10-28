(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "ex"; "eq"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs.RP"; "segs"; "@Corelib.Numbers.BinNums"; "Z"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E"; "C"; "E"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "pair"; "nil"; "app"; "bool"; "true"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "sstate"; "valuation"; "rm"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "NF"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "jpost"; "LQP"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_blocks"; "ma_s"; "malloc_rel"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "sub"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "L_malloc_ok"; "Pre_malloc"; "ok_sideK"; "EC_U"; "MInvR"; "V_RES"; "mem_kept"; "top_var"; "tp_ok"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS"; "vm_roomS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv"; "JLi_ok"; "drvN"; "malloc_cost"; "initedT"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS"; "J_payload_S"; "alloc_meta_avail"; "malloc_big_S"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_U"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "MMAP_THRESHOLD"; "kreq"; "st_init_done"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost"; "direct_case"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect_S.S"; "JLdS_core"; "J_dirS"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C"; "IEC"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect_DX"; "am_servable"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia Stdlib.Logic.FunctionalExtensionality.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocFooter OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfRepr OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfMeta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ClientLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractAM OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractDrv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.VmRoom OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.RoomS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.HeapS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractS OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ObjBytes OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.FpLaws OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZBits OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkArith OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.GapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.AllocMetaGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectPost OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapGrow OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfSlot OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectGap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.KillMap OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocDirectRun OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.DrvReach.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CallocLib.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_free__G1.Mal_free_fast OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_fast_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G1.Mal_malloc_direct_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastI OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G2.Mal_malloc_fastC OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_malloc__G3.Mal_malloc_fastD OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_runs OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_E OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G1.Mal_mdirect_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_L OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_B OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G2.Mal_mdirect_C OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_N OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G3.Mal_mdirect_D2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta__G6.Mal_ameta_sum OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_mdirect__G4.Mal_mdirect_DX OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_ameta_S.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac top_range_of L := lazymatch goal with | _ : 0x7fff7f800000 <= OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL L <= 0x7fffff800000 |- _ => fail | _ => let h := fresh "TOPR" in pose proof (OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL_val L) as h end.
Local Ltac top_ranges := repeat match goal with | |- context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] => top_range_of L | _ : context [OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout.topL ?L] |- _ => top_range_of L end.
Local Ltac lia := first [Stdlib.micromega.Lia.lia | top_ranges; Stdlib.micromega.Lia.lia].
Local Ltac nia := first [Stdlib.micromega.Lia.nia | top_ranges; Stdlib.micromega.Lia.nia].
Import RP.

Local Notation SP := SymSoundR.SP.

Lemma drvN_servable : ltac2:(tb__ "0|1|
S4S1aS2fS5R2R1A3S0S2SdS38S1cR2A1M0A1SeA3S3dG0A1A2F_;FA;Fk;").
Proof. exact U.Mal_mdirect__G4.Mal_mdirect_X3.drvN_servable. Qed.

Section S.
Hypothesis AMS : ltac2:(tb__ "0|0|
S33S3S5S3cA3").

Definition KcS (Kc : list event -> Model -> Prop) (X : Z) : list event -> Model -> Prop := ltac2:(tb__ "0|0|
S7S15A1S14S0VKc;R2R1A2S2dR1VX;A2A2Lmd;Ltr;").

Definition JLdS_core (A : MA) (X : Z) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|6|
S11S11S7S15A1S14S1S1aS1aS1S7S8S4S4A2M0A1M1G1S1G1G1S0S28S3S5R3R6R4A5S0S31VA;R3A2S0S1S7S8S37S4A2A1M2G2S1dVA;S13Q40M3SfR8PcM4A2A2R1S13G3SfR7S29A2A2R4A5Lktr;A2S0S2dR4S20VX;S30S13G3SfR7G4A2A2M5A1A2A2S0S2G1S1bR3A1ScG0R2S9G0SaS4S4S13G3SfR6S29A2A2G5A4R1A3A3A3S0S2G1S1bVA;A1ScG0R2R1A3A3S0S2aS3S5VA;R3S12R7A1S12R6A1A6VKc;R5R4A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2Lmd;Ltr;Lrho';Lrho0;").

Definition J_dirS (A : MA) (X : Z) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|1|
S11S7S15A1S14S0S28S3S5VA;R3R1A5S0S1S4S4S2fS5R1VA;A3Lk;A2S0S0S39S13Q40SfR3PcA2A2M0A1S1eG0S1fZ2Z1aA2A2A2S0VKc;R2R1A2S0S0S2dR1VX;A2S1eS30G0A1VX;A2A2S0S2cS5R3A2S2bVA;R3A2A2A2A2A2A2A2Lmd;Ltr;Lrho;").

Theorem malloc_direct_S_core : ltac2:(tb__ "0|1|
S22OF_;S1aS4S7S15A1S14OF_;F_;S11S26S3R5R2A3S21S3R6S23S3S3bR5R4R3A3S25S6A1R2A4S19S3S17R2S9S8S10S18A2M0SaS10S18S24S6A1S3aR5R4R3A3A4SbG0A1A3A4A4F_;Frho0;FKc;FX;FA;Fok;").
Proof using AMS.
  intros ok A X Kc rho0 HS. apply triple_inh. intros w0 [Hsm0w (_ & (k & HdN) & [Hn N26] & _ & [Hroom0 Hcost] & Htp & HTV0)]. pose proof (top_high_pre A rho0 w0 Hsm0w HTV0) as Htop0.
  pose proof HS as (Hok & Hokp & HVI).
  pose proof (drvN_servable k A HdN) as [Hinit HAV].
  set (QF' := LQP segs NF rho0 [(L_malloc_ok E, JLdS_core A X Kc)]).
  assert (okK_of : forall (K : list event -> Model -> Prop), (forall tr md, K tr md -> Kc tr md) -> okK ok K).
  { intros K HK. split; [eapply ok_frame_imp; [exact HK | exact Hok] | eapply ok_pframe_imp; [exact HK | exact Hokp]]. }
  assert (TR_run : forall K S fuel leaves rho (Q' : assn),
    sym_run segs fuel (md_cutsX c x) S true = Some leaves -> ss_lenient S = false -> okK ok K ->
    (forall L rho', In L leaves -> agree_below (ss_next S) rho rho' -> triple segs ok (SP segs K (lf_state L) rho') Q') ->
    triple segs ok (SP segs K S rho) Q').
  { intros K S fuel leaves rho Q' Hrun Hlen [HokK _] Hc. exact (run_tr segs ok fuel (md_cutsX c x) S leaves K rho Q' Hrun Hlen HokK Hc). }

  apply (triple_pre segs ok (SPJ segs (J_pre A (KcS Kc X)) (Pre_malloc E) rho0)).
  { intros w [Hsm (HMI & _ & _ & HKc & [Hroom _] & Htp' & HTV')]. split; [exact Hsm|]. split; [exact HMI|]. split; [split; [exact HKc | exact Hroom]|]. split; [exact Htp'|]. split; [exact Hinit | exact HTV']. }
  eapply triple_pre; [intros w Hw; exact (entry_D_call A (KcS Kc X) rho0 Hn w Hw)|].
  pose proof E_mm_shape as (Mpc & M17 & M11 & M10 & M12 & M13 & M14 & M15). pose proof E_mm_misc as (Mnx & Mecall & Mobjs & Mfacts).

  apply (TR_run (K0 A (KcS Kc X) rho0) (D_call x) 200%nat _ rho0 QF' run_call eq_refl (okK_of _ (fun tr md HK => proj1 (proj1 HK)))).
  intros L rho1 [<- | []] Hag1. cbn [lf_state].
  assert (R12 : rw rho1 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hag1); vm_compute; reflexivity).
  set (lenw := eval rho1 (reg E_mm 11)).
  assert (Hlen : bv_unsigned lenw = bv_unsigned (rw rho0 12%positive) + 20).
  { unfold lenw. rewrite M11. pose proof Hn as [N1 N2]. unfold MallocModel.MMAP_THRESHOLD, IB, UNIT in N1.
    rewrite (U_addc rho1 (v 12) 20 (bv_unsigned (rw rho0 12%positive))); [reflexivity | cbn [eval U.Mal_malloc__G1.Mal_malloc_direct_runs.v]; rewrite R12; reflexivity | lia | lia]. }
  pose proof (mmap_nZ_le lenw) as NZ1. pose proof (mmap_nZ_ge lenw) as NZ2. pose proof (urange (rw rho0 12%positive)) as UR.
  unfold malloc_cost in Hcost.
  set (X1 := X - mmap_nZ lenw).

  eapply triple_seq.
  { apply triple1_triple. change (SP segs (K0 A (KcS Kc X) rho0) E_mm rho1) with (SPJ segs (liftK (K0 A (KcS Kc X) rho0)) E_mm rho1).
    apply (triple1_mmap_rwJ_forced segs ok (liftK (K0 A (KcS Kc X) rho0)) (fun _ _ _ => False) (Jo A (KcS Kc X1) rho0 rho1) E_mm rho1
             (ok_frame_liftK segs ok _ (proj1 (okK_of _ (fun tr md HK => proj1 (proj1 HK))))) (ok_pframe_liftK ok _ (proj2 (okK_of _ (fun tr md HK => proj1 (proj1 HK))))) Mecall M17).
    intros tr ms md Hsp [[HKc Hroom] HMI].
    pose proof (pending_args segs rho1 E_mm tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
    change (reg_sv E_mm 11) with (reg E_mm 11) in G1. change (reg_sv E_mm 12) with (reg E_mm 12) in G2. change (reg_sv E_mm 13) with (reg E_mm 13) in G3.
    change (reg_sv E_mm 14) with (reg E_mm 14) in G4. change (reg_sv E_mm 15) with (reg E_mm 15) in G5. change (reg_sv E_mm 10) with (reg E_mm 10) in G0.
    rewrite M10 in G0. rewrite M12 in G2. rewrite M13 in G3. rewrite M14 in G4. rewrite M15 in G5. cbn [eval] in G0, G2, G3, G4, G5. fold lenw in G1.
    assert (Hpos : 0 < bv_unsigned lenw) by (clear - Hlen UR; lia).
    assert (HXl : mmap_nZ lenw <= X) by (clear - Hlen UR NZ1 Hcost; lia).
    split; [rewrite G1; intros E0; apply (f_equal bv_unsigned) in E0; rewrite Hlen in E0; change (bv_unsigned (Z_to_bv 64 0)) with 0 in E0; pose proof Hn as [N1 _]; unfold MallocModel.MMAP_THRESHOLD in N1; lia|].
    split; [apply mmap_modeled_b_intro; [rewrite G2; reflexivity | rewrite G3; reflexivity | rewrite G5; reflexivity]|].
    split; [rewrite G3; apply mmap_noreserve_b_34; reflexivity|].
    split.
    {   rewrite G1. intros Hrf. exact (vm_roomS_rw_refused_False md X lenw (ms_gpr ms 3) Hroom Hpos HXl ltac:(rewrite G3; apply mmap_noreserve_b_34; reflexivity) Hrf). }
    intros a Hpl. pose proof Hpl as (Hal & Hpos' & HceilT & Hfree & _). rewrite G1 in HceilT, Hfree |- *.
    destruct (mmap_nw _ a lenw HceilT) as [En Hnw].
    pose proof HceilT as Hceil. rewrite <- (vm_ok_top _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 HMI)))))) in Hceil.
    assert (FREE : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) ->
              forall y, bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e) -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros [ea esz] He y Hy Hin. pose proof (region_free_In _ _ _ _ _ Hfree He) as OV. unfold iv_overlap in OV. cbn [fst snd] in Hy.
      rewrite En in OV. apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia. }
    assert (MISS : forall y, mc_img_lo C <= y < mc_img_hi C -> ~ (bv_unsigned a <= y < bv_unsigned a + mmap_nZ lenw)).
    { intros y Hy. pose proof HMI as XM. unfold MInv in XM. cbn zeta in XM. destruct XM as (_ & _ & _ & _ & _ & _ & _ & _ & HIR & _).
      destruct (HIR y Hy) as (e & He & Hey). exact (FREE e ltac:(apply in_app_iff; left; exact He) y Hey). }
    split.
    -
      intros o Ho. pose proof (in_map (fun o => (ob_base o, ob_lo o, ob_hi o)) _ _ Ho) as RO. rewrite Mobjs in RO. destruct RO as [RO|[]]. symmetry in RO. injection RO as Eb El Eh.
      pose proof (smatch_pending_mem segs _ _ _ _ _ Hsp) as (Hall & _ & _). pose proof (smatch_pending_facts segs _ _ _ _ _ Hsp) as Hfacts. cbn [fst snd cfg_ms cfg_model] in Hall, Hfacts.
      assert (HF3 : Forall (SymState.holds rho1) D_win_facts) by (apply (Forall_inclb rho1 _ (ss_facts E_mm)); [exact Mfacts | exact Hfacts]).
      pose proof (window_facts segs rho1 ms malloc_stack o ltac:(unfold malloc_stack; lia) HF3 Eb El (proj1 (Forall_forall _ _) Hall o Ho)) as (W1 & W2 & W3 & W4 & W5 & W6 & WS).
      assert (TOPW1 : topL (ma_L A) <= bv_unsigned (rw rho1 10%positive) + toS 64 (bv_unsigned (rw rho1 15%positive))) by (pose proof Htop0 as T; unfold top_high, V_DEPTH in T; rewrite <- (proj1 Hag1 10%positive), <- (proj1 Hag1 15%positive) by (cbv; reflexivity); exact T).
      unfold obj_range, obj_lo_of, obj_hi_of. rewrite Eb, El, Eh. unfold V_DEPTH in *. cbn [eval]. rewrite WS, soff_lit_small by lia. unfold SymState.ranges_disjoint. cbn [fst snd]. lia.
    - split.
      + intros y Hy. apply ro_addr_outside_image. intros Himg. exact (MISS (bv_unsigned y) Himg Hy).
      + cbn [liftK]. exists (m_vmmaps md). split; [exact HMI|]. split; [|split; [split; [exact (vm_insensitive_maps Kc HVI _ _ _ HKc) |]| reflexivity]].
        * split; [exact Hal|]. split; [exact Hpos'|]. split; [exact Hceil|]. exact FREE.
        * unfold X1. exact (vm_roomS_grant_rw md X lenw a (ms_gpr ms 0) (ms_gpr ms 3) Hroom Hpos HXl ltac:(rewrite G1 in Hpl; exact Hpl)). }

  apply triple_disj.
  { apply (triple_skip segs ok). intros w [_ F]. exact (False_ind _ F). }
  apply triple_ex. intros a.
  apply triple_SPJ_ex. intros vm0. apply triple_SPJ_pure_and. intros HMIv. apply triple_SPJ_pure_and. intros (Hal & Hpos & Hceil & Hfree).
  set (G := GCTX A (KcS Kc X1) rho0 vm0 rho1 a HMIv Htp Hn Hag1 Hal Hpos Hceil Hfree Hinit Htop0).
  assert (okK_ofS : forall K0 : list event -> Model -> Prop, (forall tr md, K0 tr md -> KcS Kc X1 tr md) -> okK ok K0).
  { intros K0 HK0. apply okK_of. intros tr md H. exact (proj1 (HK0 tr md H)). }
  change (triple segs ok (SP segs (gK1 G) (S_ret_fresh E_mm) (grhoA G)) QF').
  apply (G_granted G (triple segs ok) (okK ok) QF' (triple_pre segs ok) TR_run (okK_of _ (fun tr md HK => proj1 (proj1 HK)))).
  intros sq rho2 Hsq Hag2.
  apply (L_Xam G false (triple segs ok) (okK ok) QF' (triple_pre segs ok) (triple_inhP ok) (call_soundP segs ok)); [| | | | | exact Hsq | exact Hag2].
  -
    intros rho. apply (AMS ok [] None U0 (gA2 G) (KcS Kc X1) rho).
    + intros tr ms md ms' [HK _]. exact (Hok tr ms md ms' HK).
    + unfold gA2. cbn [ma_s]. unfold MapGrow.s2. apply servable_s2. exact HAV.
    + exact (A2_init G).
  -
    intros rho_in rhoL tr md (A3 & HM & Hpc & Hkept & _ & _ & _ & HK). exists A3. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hkept | exact HK].
  -
    intros rho_in rhoL tr md (A3 & g & Hg & HM & Hpc & Hmb & Hkk & Hkept & Hmaps & _ & HY & HK). exists A3, g.
    split; [exact Hg|]. split; [exact HM|]. split; [exact Hpc|]. split; [exact Hmb|]. split; [exact Hkk|]. split; [exact Hkept|]. split; [exact Hmaps|]. split; [exact HK | exact HY].
  -
    intros Hf. discriminate Hf.
  -
    intros A3 g vm3 rho5 OF. destruct A3 as [s3 L3].
    assert (HX : forall rhoL tr md, fin_facts G s3 L3 g rhoL tr md -> JLdS_core A X Kc rho0 rhoL tr md).
    { intros rhoL tr md (F1 & (l1 & l2 & F2 & F3) & F4 & F5 & [F6 F7] & (ktr & F8)).
      exists (A6 G s3 L3 g), l1, l2.
      split; [exact F1|]. split; [split; [exact F5 | destruct F8 as (? & _ & HE8 & _); exact (layout_extends_top _ _ _ HE8)]|]. split.
      { exists ktr. exact F8. }
      split.
      {
        apply (vm_roomS_mono md X1); [|exact F7]. unfold X1, malloc_cost in *. rewrite Hlen in NZ1, NZ2.
        split; [|lia]. pose proof F7 as (X0 & _). unfold X1 in X0. lia. }
      split; [exact F2|]. split; [exact F3|]. split; [exact F4 | exact F6]. }
    exact (L_ok_tail G (mkMA s3 L3) g vm3 rho5 OF (triple segs ok) (okK ok) QF' (triple_pre segs ok) (triple_skip segs ok) (triple_inhP ok) TR_run okK_ofS
             (@triple_seq segs ok) (fun T P Q H => @triple_ex segs ok T P Q H) (fun T P Q H => @triple_pure segs ok T P Q H)
             (post_ok_gen G s3 L3 g vm3 rho5 OF (JLdS_core A X Kc) HX)).
Qed.

Theorem malloc_big_S_proof : ltac2:(tb__ "0|0|
S34S3S5S6A3").
Proof using AMS.
  intros ok A k X Kc rho HS. apply triple_inh. intros w0 [_ (_ & HD & Hk & Hn26 & _)].
  eapply triple_pre; [|eapply triple_post; [|exact (malloc_direct_S_core ok A X Kc rho HS)]].
  - intros w [Hsm (HMI & HD' & _ & Hn26' & HKc & HR & Htp & HTV)]. split; [exact Hsm|].
    split; [exact HMI|]. split; [exists k; exact HD'|]. split; [split; [unfold direct_case; unfold MMAP_THRESHOLD in Hn26' |- *; lia | lia]|].
    split; [exact HKc|]. split; [exact HR|]. split; [exact Htp | exact HTV].
  - intros w (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ|[]]. injection EQ as <- <-.
    cbn [w_tr w_cfg fst snd cfg_model] in HJ.
    exists (L_malloc_ok E), (JLdS_big_ok segs C A k X Kc), rho'. split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
    destruct HJ as (A' & l1 & l2 & HM & Hi & (ktr & HR) & HV & HB' & HB & HK & HKc).
    exists A', l1, l2. split; [exact HM|]. split; [exact Hi|]. split.
    {
      destruct HD as (j & Hdr & H0k & Hj). exists (Datatypes.S j). split; [|unfold DRV_OPS in *; lia].
      exact (DR_malloc C j A (bv_unsigned (rw rho 12%positive)) ktr (bv_unsigned (rw rho' V_RES)) A' Hdr Hn26 HR). }
    split; [exact HV|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK | exact HKc].
Qed.

Theorem malloc_direct_ok_S_proof : ltac2:(tb__ "0|1|
S22OF_;S1aS4S4S7S15A1S14OF_;F_;S11S26S3R6R2A3S1eS36S13Q40SfR2PcA2A2A2S21S3R8S23S3S32S3S5R7R6R5R4A6S25S6A1R3A4S19S3S17R3S9S8S10S18A2M0SaS10S18S24S6A1S2eS3S5R7R4A4A4SbG0A1A3A4A4F_;F_;Frho;FKc;FX;Fk;FA;Fok;").
Proof using AMS.
  intros ok A k X Kc rho HS Hbig.
  eapply triple_pre; [|eapply triple_post; [|exact (malloc_direct_S_core ok A X Kc rho HS)]].
  - intros w [Hsm (HMI & HD' & Hn26' & HKc & [HR HC] & Htp & HTV)]. split; [exact Hsm|].
    split; [exact HMI|]. split; [exists k; exact HD'|]. split; [split; [unfold direct_case, MallocModel.MMAP_THRESHOLD in *; lia | lia]|].
    split; [exact HKc|]. split; [split; [exact HR | unfold payload_cost, malloc_cost in *; lia]|]. split; [exact Htp | exact HTV].
  - intros w (L & JL & rho' & Hin & Hag & Hsm & HJ). destruct Hin as [EQ|[]]. injection EQ as <- <-.
    cbn [w_tr w_cfg fst snd cfg_model] in HJ.
    exists (L_malloc_ok E), (JLi_ok segs C A Kc), rho'. split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
    destruct HJ as (A' & l1 & l2 & HM & Hi & _ & _ & HB' & HB & HK & HKc).
    exists A', l1, l2. split; [exact HM|]. split; [exact Hi|]. split; [exact HB'|]. split; [exact HB|]. split; [exact HK | exact HKc].
Qed.
End S.

Theorem malloc_big_S_P_closed : malloc_big_S_U.
Proof. exact (malloc_big_S_proof alloc_meta_avail_P_proof). Qed.
Theorem malloc_direct_ok_S_P : ltac2:(tb__ "0|1|
S22OF_;S1aS4S4S7S15A1S14OF_;F_;S11S26S16R6R2A3S1eS36S13Q40SfR2PcA2A2A2S21S16R8S23S16S32S16S35R7R6R5R4A6S25S27A1R3A4S19S16S17R3S9S8S10S18A2M0SaS10S18S24S27A1S2eS16S35R7R4A4A4SbG0A1A3A4A4F_;F_;Frho;FKc;FX;Fk;FA;Fok;").
Proof. exact (malloc_direct_ok_S_proof alloc_meta_avail_P_proof). Qed.
