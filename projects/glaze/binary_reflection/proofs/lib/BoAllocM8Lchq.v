(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocM8yhq.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.SpinAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8kh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8yh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8uq.
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

Section FPGenYH.
Context {fx : FPState}.

Section EFSARMH.
  Variable Hd : word -> bool.
  Hypothesis HOFFSEG : H_off_segments BSEGS Hd.
  Hypothesis WX : wx_segs_nowrap BSEGS.
  (* [comment removed for export] *)
  Variable Hd2 : word -> bool.
  Hypothesis HOFFSEG2 : H_off_segments BSEGS Hd2.
  Variable A2 : list (Z * Z).
  Hypothesis AWF2 : A_wf A2.
  Variables (A : list (Z * Z)) (regs : bvmap 5 word) (mem rom : word -> option byte) (model : Model)
            (sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz rbeg tot mfa PGP CF T thr0 : Z) (Qok Qf : config -> Prop) (MOK MKP : Model -> Model).
  #[local] Abbreviation slot := (rbeg + 0xE0000000 + mfa).
  #[local] Abbreviation SH := ((rbeg + 0xE0000000 + mfa) / 8 + 0x7fff8000).
  #[local] Abbreviation M0 := (efs_m0 mem sp ra s0v s1v s2v s3v).
  #[local] Abbreviation M1 := (mfi_m1 M0 (at_ sp (-48)) (Z_to_bv 64 0x4f5a8) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz)
                     s4v s5v (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 0x19778) PGP).
  #[local] Abbreviation ENOMEMw := (Z_to_bv 64 (2 ^ 64 - 12) : word).
  #[local] Abbreviation SCR := (word_to_le_bytes 4 (Z_to_bv 64 0xffffffffaaaaaaaa)).
  #[local] Abbreviation MR := (efs_mr mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP).
  (* [comment removed for export] *)
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab58.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 RIz.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 rbeg.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 tot.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis Hsp : 2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Htot : 0 <= tot /\ 4 * tot <= 2 ^ 29.
  Hypothesis Hmfa : 0 <= mfa <= 2 ^ 29 /\ mfa mod 2 ^ 18 = 0.
  Hypothesis Hneed : mfa < 4 * tot <= mfa + 2 ^ 18.
  Hypothesis Hroom : mfa + 2 ^ 18 <= 2 ^ 29.
  Hypothesis Hrbeg : AIMGHI <= rbeg /\ rbeg + 2 ^ 32 < 2 ^ 63 /\ rbeg mod 4096 = 0.
  Hypothesis HRI : AIMGHI <= RIz /\ RIz + 128 <= U sp - 448.
  Hypothesis HPGP : AIMGLO <= PGP /\ PGP + 8 <= AIMGHI.
  Hypothesis HCF : AIMGLO <= CF /\ CF + 264 <= AIMGHI.
  Hypothesis Hstk : store_ok BSEGS mem (at_ sp (-448)) 448 = true.
  Hypothesis R_mfa : rdn BSEGS mem (Z_to_bv 64 (RIz + 24)) 8 = Some (LE8 (Z_to_bv 64 mfa)).
  Hypothesis C_pre : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 56)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rgpg : rdn BSEGS mem (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rgcf : rdn BSEGS mem (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)).
  Hypothesis Rdpm : rdn BSEGS mem (Z_to_bv 64 (CF + 260)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rlim : rdn BSEGS mem (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Hslot : slot + 2 ^ 18 <= U sp - 448 \/ U sp <= slot.
  Hypothesis HDmfa : hid_off Hd (RIz + 24) 8.
  Hypothesis HDpre : hid_off Hd (0x10ab58 + 56) 1.
  Hypothesis HDgpg : hid_off Hd 0x105ef8 8.
  Hypothesis HDpg : hid_off Hd PGP 8.
  Hypothesis HDgcf : hid_off Hd 0x105f08 8.
  Hypothesis HDdpm : hid_off Hd (CF + 260) 1.
  Hypothesis HDlim : hid_off Hd (CF + 144) 8.
  Hypothesis HDscr : hid_off Hd (U sp - 448) 448.
  Hypothesis HALT : m_halted model = None.
  Hypothesis LC : lazy_cover Hd (m_vm_lazy model) A.
  Hypothesis AWF : A_wf A.
  Hypothesis MI : MInv A model.
  Hypothesis NODE : forall mdlm (r1 : bvmap 5 word), same_but_materialized model mdlm -> MInv A mdlm -> m_halted mdlm = None ->
        getr r1 10 = Z_to_bv 64 slot -> getr r1 11 = Z_to_bv 64 (2 ^ 18) -> getr r1 12 = Z_to_bv 64 3 -> getr r1 13 = Z_to_bv 64 50 ->
        getr r1 14 = Z_to_bv 64 (2 ^ 64 - 1) -> getr r1 15 = Z_to_bv 64 0 ->
        forall Qok' Qf' : config -> Prop,
          katwD BSEGS (mkCfg (mkst (regupd r1 10 (Z_to_bv 64 slot)) (0x811b0 : word) (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) rom) (MOK mdlm)) Qok' Qf' ->
          katsD BSEGS (mkCfg (epend r1 (0x811ac : word) M1 rom (Z_to_bv 64 222)) mdlm) Qok' Qf'.
  Hypothesis CHILD : forall mdlm, same_but_materialized model mdlm -> MInv A mdlm ->
        (m_halted (MOK mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MOK mdlm)) A /\ MInv A (MOK mdlm))
        /\ (m_halted (MKP mdlm) = None /\ lazy_cover Hd (m_vm_lazy (MKP mdlm)) A /\ MInv A (MKP mdlm)).
  Hypothesis OKSW : forall mdlm mdl4, same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl4 -> MInv A mdl4 ->
        lazy_cover Hd2 (m_vm_lazy mdl4) A2 /\ MInv A2 mdl4.
  (* [comment removed for export] *)
  Hypothesis HT : U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 448 /\ T mod 8 = 0.
  Hypothesis HTRI : T + 4096 <= RIz \/ RIz + 128 <= T.
  Hypothesis HTSH : T + 4096 <= SH \/ SH + 2 ^ 15 <= T.
  Hypothesis HRSH : RIz + 128 <= SH \/ SH + 2 ^ 15 <= RIz.
  Hypothesis HSSH : U sp <= SH \/ SH + 2 ^ 15 <= U sp - 448.
  Hypothesis HTsl : T + 4096 <= slot \/ slot + 2 ^ 18 <= T.
  Hypothesis PH : poisonH BSEGS both_poison_tab mem (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4f5c4) (at_ sp (-48)) cpm midend thr0.
  Hypothesis PCB : Forall (fun c => c + 8 <= AIMGHI) (poison_cells both_poison_tab).
  Hypothesis GH : gctH BSEGS both_gct_tab mem (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis GB : U (gt_tsd both_gct_tab) + 8 <= U sp - 448 /\ U tp - 80 <= U sp - 448 /\ U tsdp + 8 <= U sp - 448 /\ U ctxw + 160 <= U sp - 448.
  Hypothesis GS : (U (gt_tsd both_gct_tab) + 8 <= slot \/ slot + 2 ^ 18 <= U (gt_tsd both_gct_tab)) /\ (U tp - 80 <= slot \/ slot + 2 ^ 18 <= U tp - 88)
                  /\ (U tsdp + 8 <= slot \/ slot + 2 ^ 18 <= U tsdp) /\ (U ctxw + 160 <= slot \/ slot + 2 ^ 18 <= U ctxw + 152).
  Hypothesis G1 : U (gt_tsd both_gct_tab) + 8 <= SH \/ SH + 2 ^ 15 <= U (gt_tsd both_gct_tab).
  Hypothesis G2 : U tp - 80 <= SH \/ SH + 2 ^ 15 <= U tp - 88.
  Hypothesis G3 : U tsdp + 8 <= SH \/ SH + 2 ^ 15 <= U tsdp.
  Hypothesis G4 : U ctxw + 160 <= SH \/ SH + 2 ^ 15 <= U ctxw + 152.
  Hypothesis R72 : rdn BSEGS mem (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R80 : rdn BSEGS mem (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOKT : store_ok BSEGS mem thr 4096 = true.
  Hypothesis SOKRI : store_ok BSEGS mem (Z_to_bv 64 RIz) 128 = true.
  Hypothesis HDc : Forall (fun c => hid_off Hd2 c 8) (poison_cells both_poison_tab).
  Hypothesis HDsh : hid_off Hd2 SH (2 ^ 15).
  Hypothesis HD1 : hid_off Hd2 (U (gt_tsd both_gct_tab)) 8.
  Hypothesis HD2 : hid_off Hd2 (U tp - 88) 8.
  Hypothesis HD3 : hid_off Hd2 (U tsdp) 8.
  Hypothesis HD4 : hid_off Hd2 (U ctxw + 152) 8.
  Hypothesis HDT : hid_off Hd2 T 4096.
  Hypothesis HDRI : hid_off Hd2 RIz 128.
  Hypothesis HDscr2 : hid_off Hd2 (U sp - 448) 448.
  (* [comment removed for export] *)
  Hypothesis CONT1 : forall (r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MOK mdlm) mdl5 -> MInv A2 mdl5 ->
      getr r 10 = Z_to_bv 64 1 -> getr r 2 = sp -> getr r 1 = ra ->
      getr r 8 = s0v -> getr r 9 = s1v -> getr r 18 = s2v -> getr r 19 = s3v -> getr r 20 = s4v -> getr r 21 = s5v -> getr r 4 = tp -> getr r 3 = gp ->
      (forall i : reg, In i [22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] -> getr r i = getr regs i) ->
      katwD BSEGS (mkCfg (mkst r ra (eam_3 MR sp s4v s5v thr v72 v80 RIz slot mfa) rom) mdl5) Qok Qf.
  Hypothesis CONT0K : forall (r' r : bvmap 5 word) mdlm mdl5,
      same_but_materialized model mdlm -> MInv A mdlm -> same_but_materialized (MKP mdlm) mdl5 -> MInv A mdl5 ->
      regs_agree (fun i : reg => In i efs_clob) regs r' -> efs_post sp ra s0v s1v s2v s3v 0 r' r ->
      katD BSEGS (mkCfg (mkst r ra (wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))) rom) mdl5) Qf.


  Theorem efs_map_arm_katwD_h_x : katwD BSEGS (mkCfg (mkst regs (0x4f508 : word) mem rom) model) Qok Qf.
  Proof using CONT0K CONT1 HDscr2 HDRI HDT HD4 HD3 HD2 HD1 HDsh HDc SOKRI SOKT R80 R72 G4 G3 G2 G1 GS GB GH PCB PH HTsl HSSH HRSH HTSH HTRI HT OKSW CHILD NODE MI AWF LC HALT HDscr HDlim HDdpm HDgcf HDpg HDgpg HDpre HDmfa Hslot Rlim Rdpm Rgcf Rpg Rgpg C_pre R_mfa Hstk HCF HPGP HRI Hrbeg Hroom Hneed Hmfa Htot Hret Hsp H21 H20 H19 H18 H9 H8 H13 H12 H11 H10 H3 H4 H2 H1 MKP MOK thr0 T CF PGP mfa tot rbeg RIz cpm midend v80 v72 ctxw tsdp gp tp thr s5v s4v s3v s2v s1v s0v ra sp A AWF2 A2 HOFFSEG2 Hd2 WX HOFFSEG Hd.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HRI as [RI1 RI2]. destruct Hrbeg as (RB1 & RB2 & RB3).
    destruct Hmfa as [[MF1 MF2] MF3]. destruct HT as (UT & T1 & T2 & T3). pose proof (u64_range thr) as Hthr.
    assert (SL : 0 <= slot /\ slot + 2 ^ 18 < 2 ^ 63) by lia.
    assert (HDf48 : hid_off Hd (U sp - 48) 48) by (eapply hid_off_sub; [exact HDscr | lia | lia]).
    assert (HDf112 : hid_off Hd2 (U sp - 112) 112) by (eapply hid_off_sub; [exact HDscr2 | lia | lia]).
    assert (FRAMES : forall mdlx mdly, m_halted mdlx = None -> lazy_cover Hd (m_vm_lazy mdlx) A -> same_but_materialized mdlx mdly ->
               m_halted mdly = None /\ lazy_cover Hd (m_vm_lazy mdly) A).
    { intros mdlx mdly HX LX SB. pose proof (same_but_materialized_frame mdlx mdly SB) as FR. split.
      - destruct FR as (_&_&_&_&_&_&_&_&_&_&_&_&Hh&_). rewrite Hh. exact HX.
      - destruct FR as (_ & _ & Hl & _). rewrite Hl. exact LX. }
    apply katsD_katwD.
    apply (efs_famap_katsD_h Hd HOFFSEG WX A regs mem rom model sp ra s0v s1v s2v s3v s4v s5v RIz rbeg tot mfa PGP CF Qok Qf MOK MKP
             H1 H2 H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 ltac:(lia) Htot (conj (conj MF1 MF2) MF3) Hneed Hroom (conj RB1 (conj RB2 RB3)) (conj RI1 RI2) HPGP HCF Hstk
             R_mfa C_pre Rgpg Rpg Rgcf Rdpm Rlim Hslot HDmfa HDpre HDgpg HDpg HDgcf HDdpm HDlim HDscr HALT LC AWF MI NODE CHILD).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as ((HOK & LOK & _) & _).
      destruct (FRAMES _ _ HOK LOK SB4) as [HALT4 LC4].
      destruct (OKSW mdlm mdl4 SBm MIm SB4 MI4) as [LC2 MI2].
      assert (OUT : forall x : word, (U x < U sp - 448 \/ U sp <= U x) -> (U x < slot \/ slot + 2 ^ 18 <= U x) -> MR x = mem x)
        by (intros x X1 X2; apply efs_mr_outside; [lia | exact SL | exact X1 | exact X2]).
      assert (GR : mem_grows mem MR) by apply efs_mr_grows.
      change (wbytes (zfill (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) M1) (at_ sp (-132)) SCR) with MR.
      apply (efs_after_map_katwD_x Hd2 HOFFSEG2 WX A2 r' MR rom mdl4 sp ra s0v s1v s2v s3v s4v s5v thr tp gp tsdp ctxw v72 v80 midend cpm RIz slot mfa T thr0 Qok Qf
               E2 ltac:(rewrite (AG 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H4)
               ltac:(rewrite (AG 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H3)
               E8 E9 E10 E18 E19 E20
               ltac:(rewrite (AG 21%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H21)
               (conj SP1 SP2) Hret ltac:(lia) (conj MF1 MF2) ltac:(lia) ltac:(lia) HTRI HTSH HRSH ltac:(clear - HSSH; lia)).
      + (* [comment removed for export] *)
        apply (poisonH_keep_P BSEGS both_poison_tab mem MR _ _ _ _ _ cpm midend thr0
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) PH); [intros x [X1 X2]; apply OUT; assumption | exact GR |].
        eapply Forall_impl; [|exact PCB]. cbv beta. intros c Hc z Hz. lia.
      + (* [comment removed for export] *)
        destruct GB as (B1 & B2 & B3 & B4). destruct GS as (S1 & S2 & S3 & S4).
        apply (gctH_keep_P BSEGS both_gct_tab mem MR _ tp tsdp ctxw thr
                 (fun z => (z < U sp - 448 \/ U sp <= z) /\ (z < slot \/ slot + 2 ^ 18 <= z)) GH); [intros x [X1 X2]; apply OUT; assumption | exact GR
                 | intros z Hz; cbv beta; clear - Hz B1 S1; lia | intros z Hz; cbv beta; clear - Hz B2 S2; lia
                 | intros z Hz; cbv beta; clear - Hz B3 S3; lia | intros z Hz; cbv beta; clear - Hz B4 S4; lia].
      + destruct GB as (B1 & B2 & B3 & B4). lia.
      + exact G1.
      + exact G2.
      + exact G3.
      + exact G4.
      + rewrite <- R72. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + rewrite <- R80. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT; clear - Hx UT T2 HTsl; lia.
      + eapply store_ok_mono; [exact GR | exact SOKT].
      + eapply store_ok_mono; [exact GR | exact SOKRI].
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-8) ra Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-16) s0v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-24) s1v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-32) s2v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + apply (efs_mr_slots mem sp ra s0v s1v s2v s3v s4v s5v RIz slot mfa PGP ltac:(lia) SL (-40) s3v Hslot); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8.
      + exact HDc.
      + exact HDf112.
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
      + intros r mdl5 SB5 MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3 CX.
        refine (CONT1 r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 C10 C2 C1 C8 C9 C18 C19 C20 C21 C4 C3 _).
        intros i Hi. rewrite (CX i Hi). apply AG. (lazymatch goal with |- ?G => let G' := eval unfold efs_clob in G in change_no_check G' end). cbn [In] in Hi |- *.
        repeat (destruct Hi as [<-|Hi]; [intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hi.
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 (E2 & E8 & E9 & E18 & E19 & E10 & E20) AG.
      destruct (CHILD mdlm SBm MIm) as (_ & (HKP & LKP & _)).
      destruct (FRAMES _ _ HKP LKP SB4) as [HALT4 LC4].
      set (MK := wbytes (wbytes M1 (at_ sp (-132)) SCR) (at_ sp (-132)) (word_to_le_bytes 4 (Z_to_bv 64 12))).
      assert (AGR : forall x : word, U sp - 48 <= U x < U sp -> MK x = M0 x).
      { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MK in G in change_no_check G' end).
        repeat (rewrite MemsetLibF.MemSplit.wbytes_outside; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
        apply mfi_m1_outside; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
      apply (efs_fail_katD Hd HOFFSEG WX A r' MK rom mdl4 sp ra s0v s1v s2v s3v Qf E2 Hret E10 ltac:(lia)
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-8) ra ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-16) s0v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-24) s1v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-32) s2v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               (efs_slots_ext MK mem sp ra s0v s1v s2v s3v (-40) s3v ltac:(lia) ltac:(lia) AGR ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 8))
               HDf48 HALT4 LC4 AWF MI4).
      intros r mdl5 SB5 MI5 POST.
      exact (CONT0K r' r mdlm mdl5 SBm MIm (same_but_materialized_trans _ _ _ SB4 SB5) MI5 AG POST).
  Qed.
End EFSARMH.
End FPGenYH.
End BoAllocM8yhq.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e.BoAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La.BoAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq.BoAllocM8Lkq OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMQRepF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys7c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8kh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8rh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8yh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lcq.
Import BoAllocM8yhq.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
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



Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3h.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
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
  Hypothesis N3FH : AsKSys10.AsKSys7c.N3FHq_stmt bt.
  Hypothesis QHDR_CONST : forall z, IB bt + 888 <= z < IB bt + 920 -> ~ consts_cells bt z.
  Context {qt qg : Z}.

  Theorem popBf_katwD_h_q :
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (sp ra s0v s1v s2v s3v s4v s5v tp gp : word) (tot : Z) (Qok Qf : config -> Prop),
    1 <= c <= 30 -> WFq bt st Lc FF qt qg -> AsKSys7b.qroom Lc qt qg -> RepX bt (XL c) st Lc FF M mdl -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
    r_fhole (a_reg st c) = true -> r_mapped_fa (a_reg st c) + KFAMAP <= 2 ^ 29 ->
    r_mapped_fa (a_reg st c) <= 4 * (r_mapped_user (a_reg st c) / csize c) -> a_kact st <= KCAP ->       (* [comment removed for export] *)
    let r := a_reg st c in let mfa := r_mapped_fa r in let lo := fa_beg SBEG c + mfa in
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ (AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920) /\ ~ (CTX + 152 <= z < CTX + 160)
                      /\ ~ (lo <= z < lo + KFAMAP) /\ ~ (sh_lo lo <= z < sh_lo lo + KFAMAP / 8)) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 4 = tp -> getr regs 3 = gp -> U tp = TP -> getr regs 10 = Z_to_bv 64 0x10ab58 ->
    getr regs 11 = Z_to_bv 64 (reginfo bt c) -> getr regs 12 = Z_to_bv 64 (region_beg SBEG c) -> getr regs 13 = Z_to_bv 64 tot ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    (CEIL + 448 <= U sp /\ U sp + 16 <= 2 ^ 47) -> ret_ok ra -> (0 <= tot /\ 4 * tot <= 2 ^ 29) -> (mfa < 4 * tot <= mfa + 2 ^ 18) ->
    writableZ BSEGS M (U sp - 448) (U sp) ->
    (* [comment removed for export] *)
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        let st' := add_meter (op_famap st c) 0 [(sh_lo lo, sh_lo lo + KFAMAP / 8)] 0 in
        WFq bt st' Lc FF qt qg -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a ->
            ((U sp - 448 <= U a < U sp) \/ (lo <= U a < lo + KFAMAP) \/ (sh_lo lo <= U a < sh_lo lo + KFAMAP / 8)
             \/ (T + 2872 <= U a < T + 2888) \/ (reginfo bt c + 24 <= U a < reginfo bt c + 32)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = sp -> getr r' 1 = ra ->
        getr r' 8 = s0v -> getr r' 9 = s1v -> getr r' 18 = s2v -> getr r' 19 = s3v -> getr r' 20 = s4v -> getr r' 21 = s5v -> getr r' 4 = tp -> getr r' 3 = gp ->
        getr r' 22 = getr regs 22 -> getr r' 23 = getr regs 23 -> getr r' 24 = getr regs 24 -> getr r' 25 = getr regs 25 ->
        katwD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qok Qf) ->
    (* [comment removed for export] *)
    (forall (r0 r' : bvmap 5 word) (M' : mem) mdl' st',
        (st' = st \/ st' = op_fhole st c) ->
        WFq bt st' Lc FF qt qg -> RepX bt (XL c) st' Lc FF M' mdl' ->
        same_except_vm mdl mdl' -> lazy_kept IA Lc FF mdl mdl' -> BackingAlgebra.model_ivs_wf mdl' -> m_halted mdl' = None ->
        (forall a : word, M' a <> M a -> ((U sp - 448 <= U a < U sp) /\ M' a <> None) \/ (lo <= U a < lo + KFAMAP)) ->
        regs_agree (fun i : reg => In i efs_clob) regs r0 -> efs_post sp ra s0v s1v s2v s3v 0 r0 r' ->
        katD BSEGS (mkCfg (mkst r' ra M' rom) mdl') Qf) ->
    katwD BSEGS (mkCfg (mkst regs (0x4f508%bv : word) M rom) mdl) Qok Qf.
  Proof using QHDR_CONST N3FH PCELLS CELLS MIDEND FL PGP TSDP BT_ia BT_segs.
    intros c st Lc FF M rom mdl regs sp ra s0v s1v s2v s3v s4v s5v tp gp tot Qok Qf Hc W QR RX HALT MW FH ROOM FAQ KC r mfa lo XOFF
           H1 H2 H4 H3 Etp H10 H11 H12 H13 H8 H9 H18 H19 H20 H21 Hsp Hret Htot Hneed WSTK CONT1 CONT0.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range sp) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14). fold mfa in E6, E7, E14.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & Y5 & Y6 & _). fold r mfa in Y5, Y6.
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CREST).
    assert (G_consts : 0x10000 <= TSDP /\ TSDP + 8 <= 0x663000 /\ 0x10000 <= PGP /\ PGP + 8 <= 0x663000 /\ 0x10000 + 88 <= TP /\ TP + 0x40 <= 0x663000).
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
    pose proof (pk_thread_geom bt BT_ia st Lc FF qt qg W) as (T1 & T2 & C1 & C2 & T4k & TIMG & CIMG).
    pose proof (pk_thread_geom2 bt st Lc FF qt qg W) as (TBAND & CBAND & TSP & CSP & S1 & S2 & S3).
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
    assert (YIMG : forall z, XL c z -> AIMGLO <= z < AIMGHI -> IB bt + 888 <= z < IB bt + 920).
    { intros z [Hx | Hl] Hz; [exact (proj1 (proj2 (XOFF z Hx)) Hz) | exfalso; fold RIz in Hl; lia]. }
    assert (YCTX : forall z, XL c z -> ~ (CTX + 152 <= z < CTX + 160)).
    { intros z [Hx | Hl]; [exact (proj1 (proj2 (proj2 (XOFF z Hx)))) | fold RIz in Hl; clear - Hl CSP ERI E9 E10 C1; lia]. }
    assert (XRI : forall i, RIz + 8 <= i < RIz + 128 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (XOFF i Hx) ltac:(fold RIz; lia)) | fold RIz in Hl; lia]. }
    assert (XSL : forall i, lo <= i < lo + 2 ^ 18 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [exact (proj1 (proj2 (proj2 (proj2 (XOFF i Hx)))) Hi) | fold RIz in Hl; lia]. }
    assert (XSH : forall i, SH <= i < SH + 2 ^ 15 -> ~ XL c i).
    { intros i Hi [Hx | Hl]; [apply (proj2 (proj2 (proj2 (proj2 (XOFF i Hx))))); fold SH; replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hi | fold RIz in Hl; lia]. }
    (* [comment removed for export] *)
    destruct (N3FH st Lc FF M0 mdl c qt qg W QR RP Hc FH MW HALT KC) as (AWF2 & NODEF & BUD & LEDOK).
    cbv zeta in AWF2, NODEF, BUD, LEDOK. fold r mfa lo SH in AWF2, NODEF, BUD, LEDOK. unfold KUSERMAP, KFAMAP in AWF2, NODEF, BUD, LEDOK.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 18) : word) in *.
    set (A2 := a_aa st ++ [(SH, SH + 2 ^ 18 / 8)]) in *.
    set (OKm := OKh addr size) in *.
    (* [comment removed for export] *)
    set (Hd := HID st mdl). set (Hd2 := mkH (m_vm_lazy mdl) A2).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2s : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. exact (mkH_off_zone bt BT_ia st mdl A2 z R13 Hz Hr). }
    assert (NH2ri : forall z, RIz <= z < RIz + 128 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NH2rt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_notlazy; [clear - Hz T1 T2 C1 C2 CR; lia|]. exact (pk_nolazy_rt bt st Lc FF M0 mdl qt qg W RP z Hz). }
    assert (NH2sh : forall z, SH <= z < SH + 2 ^ 15 -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply mkH_allowed. (lazymatch goal with |- ?G => let G' := eval unfold A2 in G in change_no_check G' end). apply (range_allowed_last (a_aa st) SH (SH + 2 ^ 18 / 8)); [ | | lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; lia | replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity; exact Hz].
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & AW1 & _) _]. cbn [fst] in AW1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW1.
      - pose proof AWF2 as AW. unfold A2, A_wf in AW. apply Forall_app in AW as [_ AW]. apply Forall_cons_iff in AW as [(_ & _ & AW2) _]. cbn [snd] in AW2. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact AW2. }
    assert (HOFF : forall (H : word -> bool) lo0 n, (forall z, lo0 <= z < lo0 + n -> H (Z_to_bv 64 z) = false) -> hid_off H lo0 n).
    { intros H lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    (* [comment removed for export] *)
    pose proof (pk_T_writable bt BT_segs BT_ia (XL c) st Lc FF M M0 mdl qt qg W RP D) as TWR.
    destruct (pk_junk8 M T (T + 4096) (T + 2872) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v72 & R72).
    destruct (pk_junk8 M T (T + 4096) (T + 2880) TWR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (v80 & R80).
    set (thr := Z_to_bv 64 T : word).
    assert (UT : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    apply (efs_map_arm_katwD_h_x Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx Hd2 (mkH_off_segments bt BT_ia st mdl A2 R13) A2 AWF2 (a_aa st)
             regs M rom mdl sp ra s0v s1v s2v s3v s4v s5v thr tp gp (Z_to_bv 64 TSDP) (Z_to_bv 64 CTX) v72 v80 (Z_to_bv 64 MIDEND) (Z_to_bv 8 1)
             RIz rbeg tot mfa PGP 0x19fce8 T 0 Qok Qf OKm (fun m => m)).
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
    - change (1092440 + 56) with 0x10ab90. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_pre ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_pg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_P ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ CELL_gcf ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 260) with 0x19fdec. rewrite <- (w2b1 0) by lia. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_dpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    - change (1703144 + 144) with 0x19fd78. exact (pk_const bt BT_segs (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST _ _ _ PC_lim ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
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
      destruct (NODEF mdlm SBm MIm) as (N1 & N2 & N3 & N4 & _).
      apply (node1_of_fixfree2_s r1 _ rom mdlm addr size Qok' Qf' HLm G10 G11 G12 G13 G14 G15); [ | | | | exact N1 | exact N2 | exact N3 | | exact K1].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end). apply mod4096_sum; [exact E12 | exact E14].
      + (lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. lia.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
      + (lazymatch goal with |- ?G => let G' := eval unfold size in G in change_no_check G' end). rewrite u_Z2bv by lia. exact N4.
    - (* [comment removed for export] *)
      intros mdlm SBm MIm. destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & HOK & MOKI & LZOK).
      split.
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ (lazy_cover_HID st mdl) LZOK).
      + split; [exact (halted_sbm mdl mdlm SBm HALT)|]. split; [| exact MIm].
        pose proof (same_but_materialized_frame mdl mdlm SBm) as (_ & _ & EL & _). rewrite EL. apply lazy_cover_HID.
    - (* [comment removed for export] *)
      intros mdlm mdl4 SBm MIm SB4 MI4. split; [| exact (BUD mdlm mdl4 SBm SB4 MI4)].
      destruct (NODEF mdlm SBm MIm) as (_ & _ & _ & _ & _ & _ & LZOK).
      pose proof (same_but_materialized_frame _ _ SB4) as (_ & _ & EL & _). rewrite EL.
      exact (lazy_cover_sub Hd2 _ _ _ (lazy_cover_mkH (m_vm_lazy mdl) A2 (m_vm_lazy mdl) (incl_refl _)) LZOK).
    - destruct (pos_mod4096 T T1 T4k) as [T4 T8]. split; [exact UT|]. split; [exact T4|]. split; [lia | exact T8].
    - clear - TSP ERI E9 E10. lia.
    - rewrite <- ESH. clear - TBAND SHB0 SHB1. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ESH. right. lia.
    - rewrite <- ELO. clear - TSP SL0 SL1. lia.
    - rewrite <- ELO.
      apply (pk_poisonH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl RP D YIMG QHDR_CONST lo (Z_to_bv 64 325060) (at_ sp (-48)));
        [(lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); lia | lia | exact SL8 | rewrite at_u by lia; lia | rewrite at_u by lia; lia | | apply ret_ok_lit; [lia | reflexivity]].
      intros i Hi. rewrite at_u in Hi by lia. apply WSTK. lia.
    - eapply Forall_impl; [| exact both_poison_cells_img]. cbv beta. intros c0 [_ Hc0]. exact Hc0.
    - apply (pk_gctH bt BT_segs BT_ia TP TSDP PGP FL MIDEND CELLS (XL c) st Lc FF M M0 mdl qt qg W RP D YIMG QHDR_CONST YCTX (at_ (at_ sp (-48)) (-16)) tp Etp);
        [rewrite !at_u by (rewrite ?at_u by lia; lia); lia | rewrite !at_u by (rewrite ?at_u by lia; lia); lia |].
      intros i Hi. rewrite !at_u in Hi by (rewrite ?at_u by lia; lia). apply WSTK. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite Etp. rewrite <- ELO.
      split; [left; lia|]. split; [left; lia|]. split; [left; lia|]. clear - CSP SL0 SL1. lia.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite Etp. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. left. lia.
    - rewrite !u_Z2bv by lia. rewrite <- ESH. clear - CBAND SHB0 SHB1. lia.
    - replace (at_ thr 2872) with (Z_to_bv 64 (T + 2872)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R72.
    - replace (at_ thr 2880) with (Z_to_bv 64 (T + 2880)) by (apply bv_eq; rewrite at_u by lia; rewrite u_Z2bv by lia; lia). exact R80.
    - apply (writableZ_sok M T (T + 4096)); [exact TWR | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - apply (writableZ_sok M RIz (RIz + 128)); [apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW] | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells, both_poison_tab in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm] in G in change_no_check G' end).
      repeat (constructor; [apply HOFF; intros z Hz; apply NH2s; lia|]). constructor.
    - rewrite <- ESH. apply HOFF. exact NH2sh.
    - (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite Etp. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2s; lia.
    - rewrite u_Z2bv by lia. apply HOFF. intros z Hz. apply NH2rt. right. lia.
    - apply HOFF. intros z Hz. apply NH2rt. left. lia.
    - apply HOFF. exact NH2ri.
    - apply HOFF. intros z Hz. apply NH2s; lia.
    - (* [comment removed for export] *)
      intros r' mdlm mdl5 SBm MIm SB5 MI5 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q4 Q3 QX.
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
      assert (WRIM : writableZ BSEGS M RIz (RIz + 128)) by (apply (repx_wr (XL c) M M0 D); [lia | lia | exact GW]).
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
      assert (W' : WFq bt (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF qt qg).
      { exact (BoAllocM8Lcq.WFq_meter0 bt (op_famap st c) Lc FF [(SH, SH + 2 ^ 18 / 8)] (OPS_WFq_famap_pf bt st Lc FF c W Hc ROOM FAQ)). }
      assert (RX' : RepX bt (XL c) (add_meter (op_famap st c) 0 [(SH, SH + 2 ^ 18 / 8)] 0) Lc FF M' mdl5).
      { apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => XL c z /\ ~ False) (XL c)); [intros z [Hz _]; exact Hz|].
        apply (repx_step bt (XL c) (fun _ => False)
                 (fun z => (U sp - 448 <= z < U sp) \/ (lo <= z < lo + 2 ^ 18) \/ (SH <= z < SH + 2 ^ 15) \/ (T + 2872 <= z < T + 2888) \/ (RIz + 24 <= z < RIz + 32))
                 Xdec_false st _ Lc Lc FF FF M M' mdl mdl5 RX FOOTM ltac:(intros a F; destruct F)).
        intros N0 N0' RPn Dn DIFF _ SAME.
        assert (EQF : forall a : word, ~ XL c (U a) -> N0' a = M' a) by (intros a Ha; apply SAME; exact (repx_off (XL c) M N0 Dn a Ha)).
        pose proof RPn as (_ & _ & _ & R4n & _). destruct (R4n c Hc) as [(_ & _ & _ & _ & _ & _ & _ & _ & _ & GWn) _]. rewrite BT_segs in GWn. fold RIz in GWn.
        destruct LED as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13).
        apply (OPS_REPq_famap_pf bt st Lc FF N0 N0' mdl mdl5 c qt qg W RPn Hc ROOM); rewrite ?BT_segs.
        - intros a Ha. destruct (DIFF a Ha) as [[F | []] Dd]. split; [|exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_famap, fslot in G in change_no_check G' end). fold r mfa lo RIz SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, T_UNW in G in change_no_check G' end).
          replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. clear - F SP1 CR. lia.
        - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). fold r mfa RIz. rewrite (rdn_ext BSEGS 8 N0' M' (Z_to_bv 64 (RIz + 24))); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | ].
          + (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). exact (eam_3_mfa BSEGS MR sp s4v s5v thr v72 v80 RIz lo mfa ltac:(lia)).
          + intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply EQF. apply XRI. lia.
        - fold RIz. apply (repx_wr (fun _ => True) N0' N0 (fun a Ha => conj I (proj2 (DIFF a Ha)))); [lia | lia | exact GWn].
        - fold r mfa lo. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP in G in change_no_check G' end). apply writableZ_of_def; [lia | lia |]. intros i Hi.
          rewrite (EQF (Z_to_bv 64 i)) by (rewrite u_Z2bv by lia; apply XSL; exact Hi). apply DEFSL. rewrite u_Z2bv by lia. exact Hi.
        - fold r mfa lo SH. (lazymatch goal with |- ?G => let G' := eval unfold KFAMAP, fillZ, byteZ, cellN in G in change_no_check G' end). replace (2 ^ 18 / 8) with (2 ^ 15) by reflexivity. intros i Hi.
          rewrite w2b1 by ((lazymatch goal with |- ?G => let G' := eval unfold FA in G in change_no_check G' end); lia).
          rewrite (rdn_ext BSEGS 1 N0' M' (Z_to_bv 64 i)); [ | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; apply EQF, XSH; lia].
          replace i with (lo / 8 + 2147450880 + (i - SH)) by lia.
          exact (eam_3_fill BSEGS MR sp thr v72 v80 RIz lo ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite <- ESH2; right; lia)
                   ltac:(rewrite <- ESH2, UT; clear - TBAND SHB0 SHB1; lia) ltac:(rewrite <- ESH2; right; lia) ltac:(rewrite <- ESH2; right; lia) s4v s5v mfa (i - SH) ltac:(lia)).
        - exact L1. - exact L2. - exact L3. - exact L4. - exact L5. - exact L6. - exact L7. - exact L8. - exact L9. - exact L10. - exact L11. - exact L12.
        - exact MI5.
        - exact L13. }
      apply (CONT1 r' M' mdl5 W' RX' SEV LK MW5 HL5); [| exact Q10 | exact Q2 | exact Q1 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21 | exact Q4 | exact Q3
                                                      | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10 | apply QX; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10].
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
      apply (CONT0 r0 r' MK mdl5 st (or_introl eq_refl) W); [ | exact (same_but_materialized_except_vm _ _ SBK) | exact (lazy_kept_sbm bt Lc FF mdl mdl5 SBK)
                                                              | exact (model_ivs_wf_sbm mdl mdl5 SBK MW) | exact (halted_sbm mdl mdl5 SBK HALT) | | exact AG | exact POST].
      + apply (repx_frame_step_q bt (XL c) st Lc FF M MK mdl mdl5 qt qg W RX); [| exact MI5 | exact SBK].
        intros a Ha. destruct (FOOTK a Ha) as [IN Dd]. split; [|exact Dd].
        intros RCa. pose proof (rep_cells_lt_ceil_q bt BT_ia st Lc FF (U a) qt qg W RCa). lia.
      + intros a Ha. left. exact (FOOTK a Ha).
  Qed.


End L3h.
End WithCeil.
