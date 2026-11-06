(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.

Module V_PHsgd.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Definition vep_error_inl_post (ret : Z) (sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (H : henv) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 a3 a4 m',
      ms' = MS (mkR (Z_to_bv 64 ret) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - VEPERR_STACK, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ henv_ok LayoutP0 VI0 H m' /\ stk rsegs m' lo (bv_unsigned sp).

  Lemma vep_error_inl :
    forall (site ret : Z) (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (H : henv) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      (site = 0x1a444 /\ ret = 0x1a484) \/ (site = 0x1a54c /\ ret = 0x1a58c) ->
      s0 = Z_to_bv 64 VEP ->
      rw_cells rsegs m VEP (vep_cells v tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      v Fvc = h_vc H -> henv_ok LayoutP0 VI0 H m -> henv_geom H -> img_ok0 m ->
      4096 <= VEP -> VEP mod 8 = 0 -> VEP + 312 <= alloc_ceiling ->
      stk rsegs m lo (bv_unsigned sp) -> lo + VEPERR_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      bv_unsigned sp <= h_sp H ->
      mem_inv rsegs m ->
      evt rsegs (vep_error_inl_post ret sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc H lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 site) fc None m (seg_rom rsegs)).
  Proof.
    intros site ret VEP v tag q H lo. intros until m.
    intros SITE S0 VEPC TAG PADS EVC HENV HG IMG VLO V8 VHI ST LO CEIL SPH MI.
    rewrite S0. unfold VEPERR_STACK in *.
    pose proof alloc_ceiling_val as ACV.
    (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    (* [comment removed for export] *)
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
    (* [comment removed for export] *)
    destruct HENV as [GLOB HOBJ].
    (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS.
    cbn [al_segs LayoutP0] in CP, CNT.
    (first [ pose proof (HOBJ) as dR_3; dand3 dR_3 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
    (first [ dand4 IMG as _ _ GVSC _ | destruct IMG as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
    (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    destruct SITE as [[-> ->]|[-> ->]].
    all: (* [comment removed for export] *)
         do 8 zstep.
    all: (* [comment removed for export] *)
         do 8 zstep.
    all: (* [comment removed for export] *)
         carve_frame 48%nat ST.
    all: do 8 zstep.
    all: try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp).
    all: release_frame FR ST (bv_unsigned sp).
    all: destruct (rw_cells_forget _ _ _ _ CNT) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear CNT.
    (* [comment removed for export] *)
    all: apply evt_done; unfold vep_error_inl_post.
    all: do 6 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [|exact ST].
    all: split; [ eapply (glob_ok_intro LayoutP0); [exact EBSS| rewrite EBSS; cbn [vi_bss VI0 al_segs LayoutP0]; exact BSS | exact CP | exact CNT']
                | eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|];
                  intros a Ha; unfold h_req, h_resp, h_hd in Ha; cbn [outside]; lia ].
  Qed.
End S.
End V_PHsgd.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHsgd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.

Module V_PH2vn.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  (* [comment removed for export] *)
  Definition txml_warn_post (E : penv) (gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (a2 : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 0x1a4d0) (Z_to_bv 64 (pe_sp E)) gp tp t0 t1 t2 (Z_to_bv 64 (pe_VEP E)) s1
                    (Z_to_bv 64 0) (Z_to_bv 64 67) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1a4d0) fc None m' (seg_rom rsegs)
      /\ munch [(pe_sp E - 48, pe_sp E)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (pe_sp E).

  Lemma txml_warn :
    forall (site : Z) (E : penv) (v : vep) (tag : list byte) (q : vep_pads) (j0 j8 : word) (lo : Z),
    forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      (site = 0x1a4b8 \/ site = 0x1a364) ->
      rw_cells rsegs m (pe_VEP E) (vep_cells v tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      v Fvc = h_vc (pe_H E) -> henv_ok LayoutP0 VI0 (pe_H E) m -> henv_geom (pe_H E) ->
      rw_cells rsegs m (pe_sp E) (pframe E j0 j8) ->
      4096 <= pe_VEP E -> pe_VEP E + 312 <= alloc_ceiling ->
      stk rsegs m lo (pe_sp E) -> lo + 48 <= pe_sp E -> alloc_ceiling <= lo ->
      mem_inv rsegs m ->
      evt rsegs (txml_warn_post E gp tp t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
        (MS (mkR ra (Z_to_bv 64 (pe_sp E)) gp tp t0 t1 t2 (Z_to_bv 64 (pe_VEP E)) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 site) fc None m (seg_rom rsegs)).
  Proof.
    intros site E v tag q j0 j8 lo. intros until m.
    intros SITE VEPC TAG PADS EVC HENV HG FR VLO VHI ST LO CEIL MI.
    pose proof alloc_ceiling_val as ACV.
    (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
    assert (PSP : pe_sp E = h_sp (pe_H E) - 176) by reflexivity.
    assert (Evc : h_vc (pe_H E) = h_sp (pe_H E) + 1304) by reflexivity.
    assert (Ewrk : h_wrk (pe_H E) = h_sp (pe_H E) + 1120) by reflexivity.
    (* [comment removed for export] *)
    destruct HENV as [GLOB HOBJ].
    (first [ pose proof (HOBJ) as dR_2; dand3 dR_2 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_al_segs. unfold vc_cells in VC. unfold wrk_cells in WK.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
    (first [ pose proof (PADS) as dR_5; dand7 dR_5 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite pframe_size in FRB. unfold pframe in FR.
    pose proof (munch_refl [(pe_sp E - 48, pe_sp E)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    destruct SITE as [-> | ->]; [do 6 zstep | do 7 zstep].
    (* [comment removed for export] *)
    all: carve_frame 48%nat ST.
    all: do 8 zstep.
    all: try replace (pe_sp E + -48 + 48) with (pe_sp E) by lia.
    all: release_frame FR0 ST (pe_sp E).
    all: replace (pe_sp E + -48) with (pe_sp E - 48) in MU by lia.
    all: apply evt_done; unfold txml_warn_post.
    all: do 2 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption| exact ST].
  Qed.

  #[using="HMC"] Lemma PH_TestXml : handler_stmt S_TestXml.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    assert (CKPT : forall q, x_p x <= q -> q <= pe_e E ->
      pinv E (PST q S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A m
      /\ hstep E x (PST q S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A A m m).
    { intros q LQ QE. split.
      - apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
        + (* [comment removed for export] *) clear - VERP LQ. lia.
        + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
      - eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| unfold pframe; exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 9) by (unfold phi, rank; rewrite ST; reflexivity).
    (* [comment removed for export] *)
    assert (TAIL_E : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc -> x_p xc = pe_e E -> x_st xc = S_TestXml ->
      realizes rsegs (mkCfg (loop_ms E 0x1a314 (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc EPc STc.
      clear - HMC PE KL PIc AINVc HSc EPc STc MDL MDH.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) (x_p xc) 0 0x1a324);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | rewrite EPc; clear; lia | left; reflexivity | clear; lia | reflexivity
        | rewrite STc; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = S_TestXml) by (rewrite EX1; exact STc).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in EPc.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x1) S_TestXml
                      (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. rewrite EPc. intros H. exfalso. clear - H. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ. }
    (* [comment removed for export] *)
    assert (NONLWS : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc -> x_p x <= x_p xc -> x_p xc < pe_e E -> x_st xc = S_TestXml ->
      realizes rsegs (mkCfg (loop_ms E 0x1a334 (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc LQ QE STc.
      clear - HMC PE KL PHI PIc AINVc HSc LQ QE STc MDL MDH.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) (x_p xc) 0 0x1a344);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | clear - QE; lia | left; reflexivity | clear; lia | reflexivity
        | rewrite STc; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = S_TestXml) by (rewrite EX1; exact STc).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PHI PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 LQ QE.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in LQ, QE.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      (first [ pose proof ((look_read rsegs E x1 _ DBY ltac:(clear - VERP; lia) QE)) as dR_6; dex1 dR_6 as b; dand3 dR_6 as Hnth Hlook RDP | pose proof ((look_read rsegs E x1 _ DBY ltac:(clear - VERP; lia) QE)) as dR_6; dand4 dR_6 as b Hnth Hlook RDP | destruct (look_read rsegs E x1 _ DBY ltac:(clear - VERP; lia) QE) as (b & Hnth & Hlook & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (WARN : forall (site : Z) (a1x : word), (site = 0x1a4b8 \/ site = 0x1a364) ->
          evt rsegs (rz_at rsegs md1 T)
              (loop_ms E site (x_p x1) (Z_to_bv 64 0x1a344) t0'' t1'' t2'' (Z_to_bv 64 (bv_unsigned b)) a1x a2'' a3'' a4'' a5'' a6'' a7'' s7'
                       t3'' t4'' t5'' t6'' mc))
      end.
      { intros site a1x SITE. unfold loop_ms.
        hide STK. hide_slow.
        call_fr (txml_warn site E (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                           (x_tag x1) (x_q x1) j0 j8 (pe_lo E)) by idtac.
        1:{ exact SITE. }
        1:{ unfold vep_cells; psimp; rewrite STATE; exact VEPC. }
        1:{ exact TAG. }
        1:{ exact PADS. }
        1:{ psimp; exact (proj1 BASE). }
        1:{ eapply (henv_stores E _ _ _ _ _ _ PE0 AINV' MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV]. }
        1:{ exact HG. }
        1:{ unfold pframe; exact FR. }
        1:{ exact VEPlo. }
        1:{ exact VEPhi. }
        1:{ unhide STK; exact STK. }
        1:{ rewrite PSP; clear - LOP; lia. }
        1:{ exact CEIL. }
        1:{ assumption. }
        clear STK. unhide_slow. rename POST into STK.
        (* [comment removed for export] *)
        zstep. zstep.
        apply rz_stop.
        match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
          assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
            by (eapply (henv_stores E A1 _ _ md1 _ _ PE0 AINV' MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
        end.
        eapply (KL (PST (x_p x1) S_NotXml
                        (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (st0 S_NotXml))
                        (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
        2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
        2:{ exact MDF. }
        2:{ eapply hstep_trans; [exact HS2|].
            eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
        2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ QE. lia. }
        apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { apply (WARN 0x1a4b8). left; reflexivity. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K2; zify_cond K2.
      2:{ (* [comment removed for export] *) apply (WARN 0x1a364). right; reflexivity. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A1 _ _ md1 _ _ PE0 AINV' MU WM WZ); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV HVSC G2 PSP; lia| exact HENV])
      end.
      eapply (KL (PST (x_p x1 + 1) S_StartTag
                      (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (st0 S_StartTag))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ QE. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
      + (* [comment removed for export] *) clear - VERP. lia.
      + (* [comment removed for export] *) clear - QE. unfold pe_e, pe_N in *. lia. }
    (* [comment removed for export] *)
    assert (LOOP : forall (k : nat) (q : Z) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a1f0 q ra' t0' t1' t2' (Z_to_bv 64 (pe_e E - q)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' m)).
    { induction k as [|k IH]; intros until t6'; intros Hk LQ QE.
      { exfalso. clear - Hk QE. lia. }
      unfold loop_ms.
      (* [comment removed for export] *)
      (first [ pose proof ((payload_read rsegs E m q DBY ltac:(clear - LQ VERP; lia) QE)) as dR_7; dex1 dR_7 as b; destruct dR_7 as [Hnth RDP] | pose proof ((payload_read rsegs E m q DBY ltac:(clear - LQ VERP; lia) QE)) as dR_7; dand3 dR_7 as b Hnth RDP | destruct (payload_read rsegs E m q DBY ltac:(clear - LQ VERP; lia) QE) as (b & Hnth & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      pose proof (vct_read0 m (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      (* [comment removed for export] *)
      zstep. zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop. destruct (CKPT q LQ ltac:(clear - QE; lia)) as [PIc HSc].
        eapply (NONLWS (PST q S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) m);
          [exact PIc| exact AINV| exact HSc| exact LQ| exact QE| reflexivity]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      - replace (pe_e E - q + -1) with (pe_e E - (q + 1)) by (clear; lia).
        eapply (IH (q + 1)); [clear - Hk; lia| clear - LQ; lia| clear - K2 Hk QE; lia].
      - (* [comment removed for export] *)
        zstep. zstep. apply rz_stop.
        destruct (CKPT (pe_e E) ltac:(clear - PLT; lia) ltac:(clear; lia)) as [PIc HSc].
        eapply (TAIL_E (PST (pe_e E) S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) m);
          [exact PIc| exact AINV| exact HSc| reflexivity| reflexivity]. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End V_PH2vn.

Module V_PH6ek.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_Comment : handler_stmt S_Comment.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    eapply (KL (PST (x_p x) S_Until
                    (fupd (fupd (fupd (fupd (fupd (fupd (x_v x) Fesicmt_p 0) Funtil LIT_arrow) Funtil_p LIT_arrow)
                                      Funtil_s (st0 S_NxtTag)) Fesicmt 0) Fstate (st0 S_Until))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    - (* [comment removed for export] *) left. split; reflexivity.
    - (* [comment removed for export] *) intros _. split; [left; reflexivity|]. split; [unfold LIT_arrow; lia| reflexivity].
  Qed.
End S.
End V_PH6ek.

Module V_PHkde.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Mem Image RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition until_byte (U j : Z) : Z :=
  if U =? LIT_arrow then (if j =? 0 then 45 else if j =? 1 then 45 else if j =? 2 then 62 else 0)
  else (if j =? 0 then 93 else if j =? 1 then 93 else if j =? 2 then 62 else 0).

Lemma until_read : forall m U j, mem_inv rsegs m -> (U = LIT_arrow \/ U = LIT_cdata_end) -> 0 <= j <= 3 ->
  ov_read_bytes rsegs m (wa (U + j)) 1 = Some [Z_to_bv 8 (until_byte U j)].
Proof.
  intros m U j MI HU Hj.
  assert (B : bytes_at rsegs m U [Z_to_bv 8 (until_byte U 0); Z_to_bv 8 (until_byte U 1); Z_to_bv 8 (until_byte U 2); Z_to_bv 8 (until_byte U 3)]).
  { apply (ro_bytes_at rsegs m); [exact MI| | |].
    - destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; lia.
    - cbn [length]. destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; lia.
    - apply ro_bytes_b_sound. destruct HU as [-> | ->]; vm_compute; reflexivity. }
  eapply (u8ro_read rsegs m U _ j); [exact B| | lia| reflexivity].
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct X as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma until_byte_3 : forall U, until_byte U 3 = 0.
Proof. intros U. unfold until_byte. destruct (U =? LIT_arrow); reflexivity. Qed.
Lemma until_byte_range : forall U j, 0 <= until_byte U j < 256.
Proof.
  intros U j. unfold until_byte.
  destruct (U =? LIT_arrow); destruct (j =? 0); destruct (j =? 1); destruct (j =? 2); lia.
Qed.

Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_Until : handler_stmt S_Until.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    destruct (UNTL eq_refl) as (HU & UP & US).
    (* [comment removed for export] *)
    assert (TAIL_E : forall (xc : pst) (mc : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc A mc -> ainv A mc md -> hstep E x xc A A m mc -> x_p xc = pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a30c (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until t6'. intros PIc AINVc HSc EPc.
      clear - HMC PE ST PLT KL PIc AINVc HSc EPc MDL MDH.
      pose proof PIc as PIc0.
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E A [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
      2:{ (* [comment removed for export] *)
          zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
          apply rz_stop.
          eapply (KL xc A mc md); [exact PIc0| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
          rewrite EPc. intros H. exfalso. clear - H. lia. }
      zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (mark_call HMC E xc A mc md T (x_p xc) (x_p xc) 0 0x1a324);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | rewrite EPc; clear; lia | left; reflexivity | clear; lia | reflexivity
        | intros _; reflexivity | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in EPc.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x1) (x_st x1)
                      (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. rewrite EPc. intros H. exfalso. clear - H. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
      (* [comment removed for export] *)
      all: rewrite ?ST1; try assumption.
      exact (conj DELIM1 DELIM2). }
    (* [comment removed for export] *)
    assert (FOUND : forall (q u : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (x_v x) Funtil_p u) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      x_p x <= q -> q < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1aaf8 (q + 1) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc STKc LQ QE. unfold loop_ms.
      clear VEPC FR DBY STK MI.
      unfold vep_cells in VEPCc. psimp_in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. rewrite US. zstep.
      (* [comment removed for export] *)
      set (xc := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Funtil_p u) Fstate (st0 S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      match goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        pose proof (ainv_stores E A m mf md _ _ PE0 AINV MUc WMc WZ) as AINVc;
        assert (PIc : pinv E xc A mf); [| assert (HSc : hstep E x xc A A m mf)] end.
      { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        - (* [comment removed for export] *) clear - VERP LQ. lia.
        - (* [comment removed for export] *) clear - QE. unfold pe_e, pe_N in *. lia.
        - (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia. }
      { eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        apply rz_stop. eapply (TAIL_E xc); [exact PIc| exact AINVc| exact HSc| subst xc; cbn [x_p]; clear - K1; lia]. }
      (* [comment removed for export] *)
      zstep. apply rz_stop.
      eapply (KL xc A _ md); [exact PIc| exact AINVc| apply md_frame_refl; [exact MDL| exact MDH]| exact HSc|].
      subst xc. psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. clear - LQ QE. lia. }
    (* [comment removed for export] *)
    assert (EXH : forall (sv u : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (x_v x) Funtil_p u) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      (x_v x Funtil) <= u <= (x_v x Funtil) + 2 ->
      realizes rsegs (mkCfg (loop_ms E 0x1a17c sv ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc STKc HUR. unfold loop_ms.
      clear VEPC FR DBY STK MI.
      unfold vep_cells in VEPCc. psimp_in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      set (xc := PST (pe_e E) S_Until (fupd (x_v x) Funtil_p u) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      assert (PIc : pinv E xc A mc); [| assert (HSc : hstep E x xc A A m mc)].
      { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        - (* [comment removed for export] *) clear - VERP PLE. unfold pe_e, pe_N in *. lia.
        - (* [comment removed for export] *) intros _. exact (conj HU (conj HUR US)).
        - (* [comment removed for export] *) revert OUT PLE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. unfold pe_e, pe_N in *. intros; lia. }
      { eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
      apply rz_stop. eapply (TAIL_E xc); [exact PIc| exact AINVc| exact HSc| reflexivity]. }
    (* [comment removed for export] *)
    assert (ULOOP : forall (k : nat) (q u : Z) (ra' t0' t1' t2' a1' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (x_v x) Funtil_p u) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E -> (x_v x Funtil) <= u <= (x_v x Funtil) + 2 ->
      evt rsegs (rz_at rsegs md T)
          (loop_ms E 0x1a144 (q + 1) ra' t0' t1' t2' (Z_to_bv 64 (pe_e E - q)) a1' (Z_to_bv 64 u) a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc)).
    { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc STKc Hk LQ QE HUR.
      { exfalso. clear - Hk QE. lia. }
      unfold loop_ms.
      clear VEPC FR DBY STK MI.
      unfold vep_cells in VEPCc. psimp_in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E mc q DBYc ltac:(clear - LQ VERP; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (until_read mcur (x_v x Funtil) (u - (x_v x Funtil)) MIx HU ltac:(clear - HUR; lia)) as RDU end.
      replace (wa ((x_v x Funtil) + (u - (x_v x Funtil)))) with (Z_to_bv 64 u) in RDU by (unfold wa; f_equal; clear; lia).
      pose proof (until_byte_range (x_v x Funtil) (u - (x_v x Funtil))) as UBR.
      remember (until_byte (x_v x Funtil) (u - (x_v x Funtil))) as ub eqn:Eub in RDU, UBR.
      zstep. clear RDU. cbv beta.
      rewrite (unsigned_lit8 ub UBR).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        zstep. if_cases K3; zify_cond K3.
        + replace (pe_e E - q + -1) with (pe_e E - (q + 1)) by (clear; lia). replace (q + 2) with (q + 1 + 1) by (clear; lia).
          lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
            eapply (IH (q + 1) (x_v x Funtil)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; rewrite STATE; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                  | clear - Hk; lia| clear - LQ; lia| clear - K3 Hk QE; lia| clear; lia] end.
        + apply rz_stop.
          lazymatch goal with MIx : mem_inv _ ?mcur |- _ =>
            eapply (EXH _ (x_v x Funtil)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; rewrite STATE; exact VEPCc| exact FRc| exact DBYc| exact STKc| clear; lia] end.
      - (* [comment removed for export] *)
        lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
          pose proof (until_read mcur (x_v x Funtil) (u + 1 - (x_v x Funtil)) MIx HU ltac:(clear - HUR; lia)) as RDU2 end.
        replace (wa ((x_v x Funtil) + (u + 1 - (x_v x Funtil)))) with (Z_to_bv 64 (u + 1)) in RDU2 by (unfold wa; f_equal; clear; lia).
        pose proof (until_byte_range (x_v x Funtil) (u + 1 - (x_v x Funtil))) as UBR2.
        remember (until_byte (x_v x Funtil) (u + 1 - (x_v x Funtil))) as ub2 eqn:Eub2 in RDU2, UBR2.
        zstep. clear RDU2. cbv beta.
        rewrite (unsigned_lit8 ub2 UBR2).
        zstep. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
          assert (HUR' : (x_v x Funtil) <= u + 1 <= (x_v x Funtil) + 2).
          { destruct (Z.eq_dec (u + 1 - (x_v x Funtil)) 3) as [EQ3|NEQ3]; [| clear - HUR NEQ3; lia].
            exfalso. apply K2. rewrite Eub2, EQ3. apply until_byte_3. }
          zstep. zstep. zstep.
          zstep. if_cases K3; zify_cond K3.
          * replace (pe_e E - q + -1) with (pe_e E - (q + 1)) by (clear; lia). replace (q + 2) with (q + 1 + 1) by (clear; lia).
            lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
              eapply (IH (q + 1) (u + 1)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; rewrite STATE; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                          | clear - Hk; lia| clear - LQ; lia| clear - K3 Hk QE; lia| exact HUR'] end.
          * apply rz_stop.
            lazymatch goal with MIx : mem_inv _ ?mcur |- _ =>
              eapply (EXH _ (u + 1)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; rewrite STATE; exact VEPCc| exact FRc| exact DBYc| exact STKc| exact HUR'] end.
        + (* [comment removed for export] *)
          zstep. apply rz_stop.
          lazymatch goal with MIx : mem_inv _ ?mcur |- _ =>
            eapply (FOUND q (u + 1)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; rewrite STATE; exact VEPCc| exact FRc| exact DBYc| exact STKc| exact LQ| exact QE] end. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    zstep. zstep. zstep. zstep.
    eapply (ULOOP (Z.to_nat (pe_e E - x_p x)) (x_p x) (x_v x Funtil_p));
      [exact MU| exact WM| exact MI| unfold vep_cells; psimp; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact STK
      | clear - PLT; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT| exact UP].
  Qed.
End S.
End V_PHkde.

Module V_PH968.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Mem Image RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PMark V_Pa4g6 V_PH51p.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Pa4g6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHkde OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Ltac show_goal_heads := idtac; match goal with |- ?G => idtac "LEFTOVER:" G end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NxtTag : handler_stmt S_NxtTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    pose proof PI as PI0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
                          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_NxtTag -> x_p xc = pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a39c (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (x_p xc))
                               t3' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc HSc STc EPc.
      clear - HMC PE KL PIc AINVc MDFc HSc STc EPc.
      pose proof PIc as PIc0. pose proof (as_lazy_nil _ _ _ AINVc) as [MDLc MDHc].
      world_open PE PIc AINVc. unfold loop_ms.
      assert (R200 : 0 <= x_v xc Fesicmt < 2^64) by (destruct ESIC as [[E1 _]|[E1 _]]; rewrite E1; unfold LIT_arrow; clear; lia).
      assert (R208 : 0 <= x_v xc Fesicmt_p < 2^64) by (destruct ESIC as [[_ E1]|[_ E1]]; [rewrite E1| revert E1; unfold LIT_arrow]; clear; intros; lia).
      apply rz_go; [exact MDHc| exact MDLc|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        zstep. zstep. apply rz_stop.
        eapply (KL xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc|].
        rewrite EPc. intros H. exfalso. clear - H. lia. }
      (* [comment removed for export] *)
      zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
      2:{ zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - K1. lia. } clear K1.
          zstep. zstep. apply rz_stop.
          eapply (KL xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc|].
          rewrite EPc. intros H. exfalso. clear - H. lia. }
      zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. lia. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. apply rz_stop.
      eapply (mark_call HMC E xc Ac mc mdc T (x_p xc) (x_p xc) 0 0x1a3c0);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | rewrite EPc; clear; lia | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; rewrite STc in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (MDF2 : md_frame md md1) by (eapply md_frame_trans; [exact MDFc| exact MDF]).
      assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      clear - HMC PE KL PI1 AINV' MDF2 HS2 VK VERP1 LM1 OP1 ST1 EP1 EPc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in EPc.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. apply rz_stop.
      eapply (KL (PST (x_p x1) (x_st x1)
                      (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF2. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      2:{ psimp. rewrite EPc. intros H. exfalso. clear - H. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
      all: rewrite ?ST1; try assumption.
      exact (conj DELIM1 DELIM2). }
    (* [comment removed for export] *)
    assert (G2E0 : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
                          (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_NxtTag -> x_v xc Fattr = 0 -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a42c (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc HSc STc AT0 LQ PLTc.
      clear - HMC PE KL PHI PIc AINVc MDFc HSc STc AT0 LQ PLTc.
      pose proof (as_lazy_nil _ _ _ AINVc) as [MDLc MDHc].
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDHc| exact MDLc|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. apply rz_stop.
      set (xg := PST (x_p xc + 1) S_StartTag (fupd (x_v xc) Fstate (st0 S_StartTag)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        pose proof (ainv_stores E Ac mc mf mdc _ _ PE0 AINVc MU WM WZ) as AINVg;
        assert (PIg : pinv E xg Ac mf); [| assert (HSg : hstep E xc xg Ac Ac mc mf)] end.
      { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ. all: show_goal_heads.
        all: first [ clear - VERP; lia
                   | clear - PLTc; unfold pe_e, pe_N in *; lia
                   | left; exact AT0
                   | intros NZ; exact (AVSB NZ)
                   | revert OUT; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia ]. }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      eapply (KL xg Ac _ mdc); [exact PIg| exact AINVg| exact MDFc| eapply hstep_trans; [exact HSc| exact HSg]|].
      subst xg. psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. clear - LQ PLTc. lia. }
    (* [comment removed for export] *)
    assert (FOUND : forall (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
                           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_NxtTag -> x_v xc Fattr = 0 -> x_p x <= x_p xc -> x_p xc < pe_e E -> look E xc = 60 ->
      realizes rsegs (mkCfg (loop_ms E 0x1a3fc (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc HSc STc AT0 LQ PLTc LK.
      clear - HMC PE KL PHI G2E0 PIc AINVc MDFc HSc STc AT0 LQ PLTc LK.
      pose proof PIc as PIc0. pose proof (as_lazy_nil _ _ _ AINVc) as [MDLc MDHc].
      world_open PE PIc AINVc. unfold loop_ms.
      apply rz_go; [exact MDHc| exact MDLc|].
      (* [comment removed for export] *)
      zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
      2:{ zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - K1. lia. } clear K1.
          apply rz_stop. eapply (G2E0 xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact AT0| exact LQ| exact PLTc]. }
      zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. lia. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. apply rz_stop.
      eapply (mark_call HMC E xc Ac mc mdc T (x_p xc) (x_p xc) 0 0x1a414);
        [ exact PE | exact PIc0 | exact AINVc | clear; lia | clear - PLTc; lia | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; rewrite STc in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
      assert (MDF2 : md_frame md md1) by (eapply md_frame_trans; [exact MDFc| exact MDF]).
      assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (AT1 : x_v x1 Fattr = 0) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact AT0).
      assert (LK1 : look E x1 = 60) by (unfold look; rewrite EP1; exact LK).
      clear - HMC PE KL PHI G2E0 PI1 AINV' MDF2 HS2 VK VERP1 LM1 OP1 ST1 EP1 AT1 LK1 LQ PLTc.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1. rewrite <- EP1 in PLTc, LQ. clear EP1.
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        destruct (look_read rsegs E x1 mf DBY ltac:(clear - VERP Dlo; lia) PLTc) as (b & Hnth & Hlook & RD) end.
      zstep. clear RD. cbv beta. zstep. zstep. if_cases K2; zify_cond K2.
      { exfalso. apply K2. rewrite Hlook. exact LK1. }
      clear K2. apply rz_stop.
      set (xm := PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                     (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)).
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        pose proof (ainv_stores E A1 m2 mf md1 _ _ PE0 AINV' MU WM WZ) as AINVm;
        assert (PIm : pinv E xm A1 mf); [| assert (HSm : hstep E x1 xm A1 A1 m2 mf)] end.
      { subst xm. apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
        all: rewrite ?ST1; try assumption. all: try exact (conj DELIM1 DELIM2). all: show_goal_heads. }
      { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
      eapply (G2E0 xm A1 _ md1); [exact PIm| exact AINVm| exact MDF2| eapply hstep_trans; [exact HS2| exact HSm]
        | subst xm; cbn [x_st]; exact ST1| subst xm; psimp; exact AT1| subst xm; cbn [x_p]; exact LQ| subst xm; cbn [x_p]; exact PLTc]. }
    (* [comment removed for export] *)
    assert (NLOOP : forall (k : nat) (xc : pst) (Ac : AS) (mc : mem) (mdc : Model)
                           (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word),
      pe_e E - x_p xc = Z.of_nat k ->
      pinv E xc Ac mc -> ainv Ac mc mdc -> md_frame md mdc -> hstep E x xc A Ac m mc ->
      x_st xc = S_NxtTag -> x_v xc Fattr = 0 -> x_p x <= x_p xc -> x_p xc < pe_e E ->
      realizes rsegs (mkCfg (loop_ms E 0x1a254 (x_p xc) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) mdc) T).
    { induction k as [|k IH]; intros until t6'; intros Hk PIc AINVc MDFc HSc STc AT0 LQ PLTc; [exfalso; clear - Hk PLTc; lia|].
      (* [comment removed for export] *)
      assert (L2 : forall (xd : pst) (Ad : AS) (mdd : mem) (mdm : Model)
                          (ra_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word),
        pinv E xd Ad mdd -> ainv Ad mdd mdm -> md_frame md mdm -> hstep E x xd A Ad m mdd ->
        x_st xd = S_NxtTag -> x_v xd Fattr = 0 -> x_p xd = x_p xc + 1 ->
        realizes rsegs (mkCfg (loop_ms E 0x1a2f0 (x_p xc) ra_ t0_ t1_ t2_ a0_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ (Z_to_bv 64 (x_p xd))
                                 t3_ t4_ t5_ t6_ mdd) mdm) T).
      { intros until t6_. intros PId AINVd MDFd HSd STd ATd EPd.
        clear - IH TAIL Hk PId AINVd MDFd HSd STd ATd EPd LQ PLTc.
        pose proof (as_lazy_nil _ _ _ AINVd) as [MDLd MDHd].
        pose proof (pi_pe _ _ _ _ PId) as PLEd. pose proof (pi_verp _ _ _ _ PId) as VERPd.
        destruct (pi_data _ _ _ _ PId) as (LDd & _ & DLENd).
        pose proof (live_geom LayoutP0 _ _ _ _ _ AINVd LDd) as (_ & _ & Dlod & Dhid & _).
        pose proof alloc_ceiling_val as CV. unfold loop_ms. unfold pe_e, pe_N in *.
        apply rz_go; [exact MDHd| exact MDLd|].
        (* [comment removed for export] *)
        zstep. zstep. if_cases Kb; zify_cond Kb; unsign Kb.
        - apply rz_stop. eapply (IH xd Ad mdd mdm); [clear - Hk EPd Kb VERPd Dlod Dhid PLEd CV; lia| exact PId| exact AINVd| exact MDFd| exact HSd| exact STd| exact ATd
            | clear - LQ EPd; lia| clear - Kb VERPd Dlod Dhid PLEd CV; lia].
        - (* [comment removed for export] *)
          zstep. apply rz_stop. eapply (TAIL xd Ad mdd mdm); [exact PId| exact AINVd| exact MDFd| exact HSd| exact STd| clear - Kb PLEd VERPd Dlod Dhid CV; lia]. }
      clear IH TAIL.
      (* [comment removed for export] *)
      assert (G158 : forall (j : Z) (xd : pst) (Ad : AS) (mdd : mem) (mdm : Model)
                            (ra_ t0_ t1_ t2_ a1_ a2_ a3_ a4_ a5_ a6_ a7_ s7_ t3_ t4_ t5_ t6_ : word),
        pinv E xd Ad mdd -> ainv Ad mdd mdm -> md_frame md mdm -> hstep E x xd A Ad m mdd ->
        x_st xd = S_NxtTag -> x_v xd Fattr = 0 -> x_p xd = x_p xc ->
        x_v xd Fesicmt = LIT_arrow -> x_v xd Fesicmt_p = LIT_arrow + j -> 0 <= j <= 2 ->
        realizes rsegs (mkCfg (loop_ms E 0x1a2a4 (x_p xd) ra_ t0_ t1_ t2_ (Z_to_bv 64 (LIT_arrow + j)) a1_ a2_ a3_ a4_ a5_ a6_ a7_ s7_
                                 t3_ t4_ t5_ t6_ mdd) mdm) T).
      { intros until t6_. intros PId AINVd MDFd HSd STd ATd EPd EC EPJ HJ.
        clear - HMC PE L2 PId AINVd MDFd HSd STd ATd EPd EC EPJ HJ PLTc.
        pose proof PId as PId0. pose proof (as_lazy_nil _ _ _ AINVd) as [MDLd MDHd].
        world_open PE PId AINVd. unfold loop_ms. rewrite EPd. rewrite EPd in PLE.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mdd) as MU. pose proof (wmono_refl rsegs mdd) as WM.
        assert (WZ : wzone E Ad [pe_S E; vb_buf (x_vv xd); pe_DATA E; x_v xd Fattr_vsb; oabuf xd; x_v xd Finclude_src; oibuf xd]
                             [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        rewrite EPJ in VEPC.
        apply rz_go; [exact MDHd| exact MDLd|].
        (* [comment removed for export] *)
        zstep. zstep.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
          pose proof (until_read mf LIT_arrow (j + 1) ltac:(assumption) (or_introl eq_refl) ltac:(clear - HJ; lia)) as RU end.
        replace (LIT_arrow + (j + 1)) with (LIT_arrow + j + 1) in RU by (clear; lia).
        pose proof (until_byte_range LIT_arrow (j + 1)) as UBR.
        assert (LAR : 0 <= LIT_arrow + j + 1 < 2^64) by (unfold LIT_arrow; clear - HJ; lia).
        zstep. clear RU. cbv beta.
        (* [comment removed for export] *)
        zstep. zstep. if_cases Kz; zify_cond Kz.
        - (* [comment removed for export] *)
          assert (HJ1 : j + 1 <= 2).
          { destruct (Z.eq_dec (j + 1) 3) as [J3|NJ3]; [| clear - HJ NJ3; lia].
            exfalso. apply Kz. rewrite J3, until_byte_3. reflexivity. }
          apply rz_stop.
          set (xg := PST (x_p xc + 1) S_NxtTag (fupd (x_v xd) Fesicmt_p (LIT_arrow + j + 1)) (x_tag xd) (x_q xd) (x_vv xd) (x_va xd) (x_vi xd)).
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            pose proof (ainv_stores E Ad mdd mf mdm _ _ PE0 AINVd MU WM WZ) as AINVg;
            assert (PIg : pinv E xg Ad mf); [| assert (HSg : hstep E xd xg Ad Ad mdd mf)] end.
          { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINVd MU WM WZ.
            all: first [ clear - VERP EPd; lia
                       | clear - PLTc; unfold pe_e, pe_N in *; lia
                       | right; split; [exact EC| clear - HJ HJ1; lia]
                       | left; exact ATd
                       | intros NZ; exact (AVSB NZ)
                       | revert OUT EPd; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
                       | show_goal_heads ]. }
          { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same xd _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xd _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          eapply (L2 xg Ad _ mdm); [exact PIg| exact AINVg| exact MDFd| eapply hstep_trans; [exact HSd| exact HSg]
            | reflexivity| subst xg; psimp; exact ATd| subst xg; cbn [x_p]; reflexivity].
        - (* [comment removed for export] *)
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply rz_stop.
          set (xe := PST (x_p xc) S_NxtTag (fupd (fupd (fupd (fupd (x_v xd) Fesicmt_p (LIT_arrow + j + 1)) Fesi_found 1) Fesicmt 0) Fesicmt_p 0)
                         (x_tag xd) (x_q xd) (x_vv xd) (x_va xd) (x_vi xd)).
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            pose proof (ainv_stores E Ad mdd mf mdm _ _ PE0 AINVd MU WM WZ) as AINVe;
            assert (PIe : pinv E xe Ad mf); [| assert (HSe : hstep E xd xe Ad Ad mdd mf)] end.
          { subst xe. apply Build_pinv; psimp; pinv_close PE0 AINVd MU WM WZ.
            all: first [ clear - VERP EPd; lia
                       | clear - PLE; lia
                       | left; split; reflexivity
                       | left; exact ATd
                       | intros NZ; exact (AVSB NZ)
                       | revert OUT EPd; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
                       | show_goal_heads ]. }
          { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same xd _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xd _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          assert (HSe' : hstep E x xe A Ad m _) by (eapply hstep_trans; [exact HSd| exact HSe]).
          eapply (mark_call HMC E xe Ad _ mdm T (x_p xc) (x_p xc + 1) 1 0x1a2d8);
            [ exact PE | exact PIe | exact AINVe | subst xe; cbn [x_p]; clear; lia | clear - PLTc; lia | right; reflexivity
            | clear; lia | reflexivity | intros [X|X]; discriminate X | ].
          intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 m3 md2 v2 vv2 x2 EX2 PI2 AINV2 MDF2 HS2 VK2 VERP2 LM2 OP2 CRC2 CRCP2.
          assert (HS3 : hstep E x x2 A A2 m m3) by (eapply hstep_trans; [exact HSe'| exact HS2]).
          assert (MDF3 : md_frame md md2) by (eapply md_frame_trans; [exact MDFd| exact MDF2]).
          assert (ST2 : x_st x2 = S_NxtTag) by (rewrite EX2; reflexivity).
          assert (EP2 : x_p x2 = x_p xc + 1) by (rewrite EX2; reflexivity).
          assert (AT2 : x_v x2 Fattr = 0) by (rewrite EX2; cbn [x_v after_mark]; vk_norm VK2; subst xe; psimp; exact ATd).
          clear - HMC PE L2 PI2 AINV2 MDF3 HS3 ST2 EP2 AT2.
          pose proof (as_lazy_nil _ _ _ AINV2) as [MDL2 MDH2].
          world_open PE PI2 AINV2. unfold loop_ms.
          pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
          assert (WZ : wzone E A2 [pe_S E; vb_buf (x_vv x2); pe_DATA E; x_v x2 Fattr_vsb; oabuf x2; x_v x2 Finclude_src; oibuf x2]
                               [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
          apply rz_go; [exact MDH2| exact MDL2|].
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. apply rz_stop.
          set (xs := PST (x_p x2) S_NxtTag (fupd (x_v x2) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x2 Fnm_skip))) + 1))
                         (x_tag x2) (x_q x2) (x_vv x2) (x_va x2) (x_vi x2)).
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            pose proof (ainv_stores E A2 m3 mf md2 _ _ PE0 AINV2 MU WM WZ) as AINVs;
            assert (PIs : pinv E xs A2 mf); [| assert (HSs : hstep E x2 xs A2 A2 m3 mf)] end.
          { subst xs. apply Build_pinv; psimp; pinv_close PE0 AINV2 MU WM WZ.
            all: rewrite ?ST2; try assumption. all: try exact (conj DELIM1 DELIM2). all: show_goal_heads. }
          { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same x2 _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x2 _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          (* [comment removed for export] *)
          rewrite <- EP2.
          eapply (L2 xs A2 _ md2); [exact PIs| exact AINVs| exact MDF3| eapply hstep_trans; [exact HS3| exact HSs]
            | reflexivity| subst xs; psimp; exact AT2| subst xs; cbn [x_p]; exact EP2]. }
      (* [comment removed for export] *)
      clear - HMC PE L2 G158 FOUND PIc AINVc MDFc HSc STc AT0 LQ PLTc.
      pose proof PIc as PIc0. pose proof (as_lazy_nil _ _ _ AINVc) as [MDLc MDHc].
      world_open PE PIc AINVc. unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU. pose proof (wmono_refl rsegs mc) as WM.
      assert (WZ : wzone E Ac [pe_S E; vb_buf (x_vv xc); pe_DATA E; x_v xc Fattr_vsb; oabuf xc; x_v xc Finclude_src; oibuf xc]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDHc| exact MDLc|].
      (* [comment removed for export] *)
      destruct (look_read rsegs E xc mc DBY ltac:(clear - VERP; lia) PLTc) as (b & Hnth & Hlook & RD).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RD. cbv beta. zstep. zstep. if_cases Kf; zify_cond Kf.
      { apply rz_stop. eapply (FOUND xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact AT0| exact LQ| exact PLTc
          | rewrite <- Hlook; exact Kf]. }
      (* [comment removed for export] *)
      zstep. zstep.
      destruct ESIC as [[EC0 EP0]|[EC1 [EPlo EPhi]]].
      - (* [comment removed for export] *)
        rewrite EP0. zstep. if_lit.
        apply rz_stop.
        set (xn := PST (x_p xc + 1) S_NxtTag (x_v xc) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
        assert (PIn : pinv E xn Ac mc); [| assert (HSn : hstep E xc xn Ac Ac mc mc)].
        { subst xn. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
          all: first [ clear - VERP; lia
                     | clear - PLTc; unfold pe_e, pe_N in *; lia
                     | left; split; [exact EC0| exact EP0]
                     | left; exact AT0
                     | intros NZ; exact (AVSB NZ)
                     | revert OUT; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
                     | show_goal_heads ]. }
        { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
        eapply (L2 xn Ac mc mdc); [exact PIn| exact AINVc| exact MDFc| eapply hstep_trans; [exact HSc| exact HSn]| reflexivity| exact AT0| reflexivity].
      - (* [comment removed for export] *)
        assert (HJ : 0 <= x_v xc Fesicmt_p - LIT_arrow <= 2) by (clear - EPlo EPhi; lia).
        set (j := x_v xc Fesicmt_p - LIT_arrow) in HJ.
        assert (EPJ : x_v xc Fesicmt_p = LIT_arrow + j) by (subst j; clear; lia). clearbody j.
        rewrite EPJ in VEPC |- *. clear EPlo EPhi.
        assert (LAR0 : 0 <= LIT_arrow + j < 2^64) by (unfold LIT_arrow; clear - HJ; lia).
        (* [comment removed for export] *)
        zstep. if_cases Kn; zify_cond Kn. { exfalso. revert Kn HJ. clear. unfold LIT_arrow. intros. lia. } clear Kn.
        (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
          pose proof (until_read mf LIT_arrow j ltac:(assumption) (or_introl eq_refl) ltac:(clear - HJ; lia)) as RU end.
        pose proof (until_byte_range LIT_arrow j) as UBR.
        zstep. clear RU. cbv beta.
        (* [comment removed for export] *)
        zstep. if_cases Km; zify_cond Km.
        + (* [comment removed for export] *)
          zstep. zstep. apply rz_stop.
          set (xr := PST (x_p xc + 1) S_NxtTag (fupd (x_v xc) Fesicmt_p (x_v xc Fesicmt)) (x_tag xc) (x_q xc) (x_vv xc) (x_va xc) (x_vi xc)).
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            pose proof (ainv_stores E Ac mc mf mdc _ _ PE0 AINVc MU WM WZ) as AINVr;
            assert (PIr : pinv E xr Ac mf); [| assert (HSr : hstep E xc xr Ac Ac mc mf)] end.
          { subst xr. apply Build_pinv; psimp; pinv_close PE0 AINVc MU WM WZ.
            all: first [ clear - VERP; lia
                       | clear - PLTc; unfold pe_e, pe_N in *; lia
                       | right; rewrite EC1; split; [reflexivity| clear; lia]
                       | left; exact AT0
                       | intros NZ; exact (AVSB NZ)
                       | revert OUT; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
                       | show_goal_heads ]. }
          { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same xc _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E xc _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          eapply (L2 xr Ac _ mdc); [exact PIr| exact AINVr| exact MDFc| eapply hstep_trans; [exact HSc| exact HSr]| reflexivity| subst xr; psimp; exact AT0| reflexivity].
        + (* [comment removed for export] *)
          zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
          2:{ zstep. if_cases K1; zify_cond K1. 2:{ exfalso. clear - K1. lia. } clear K1.
              apply rz_stop. eapply (G158 j xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact AT0| reflexivity| exact EC1| exact EPJ| exact HJ]. }
          zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1. lia. } clear K1.
          (* [comment removed for export] *)
          zstep. rewrite EC1. zstep. if_cases Ke; zify_cond Ke.
          { (* [comment removed for export] *)
            apply rz_stop. eapply (G158 j xc Ac mc mdc); [exact PIc0| exact AINVc| exact MDFc| exact HSc| exact STc| exact AT0| reflexivity| exact EC1| exact EPJ| exact HJ]. }
          (* [comment removed for export] *)
          assert (J0 : j = 0) by (revert Ke; clear; unfold LIT_arrow; intros; lia).
          zstep. zstep. zstep. zstep. apply rz_stop.
          eapply (mark_call HMC E xc Ac mc mdc T (x_p xc) (x_p xc) 0 0x1a294);
            [ exact PE | exact PIc0 | exact AINVc | clear; lia | clear - PLTc; lia | left; reflexivity | clear; lia | reflexivity
            | intros [X|X]; rewrite STc in X; discriminate X | ].
          intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
          assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HSc| exact HS]).
          assert (MDF2 : md_frame md md1) by (eapply md_frame_trans; [exact MDFc| exact MDF]).
          assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; exact STc).
          assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
          assert (AT1 : x_v x1 Fattr = 0) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact AT0).
          assert (ECx : x_v x1 Fesicmt = LIT_arrow) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact EC1).
          assert (EPx : x_v x1 Fesicmt_p = LIT_arrow + j) by (rewrite EX1; cbn [x_v after_mark]; vk_norm VK; exact EPJ).
          clear - HMC PE G158 PI1 AINV' MDF2 HS2 ST1 EP1 AT1 ECx EPx HJ LAR0.
          pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
          world_open PE PI1 AINV'. unfold loop_ms.
          pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
          assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                               [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
          apply rz_go; [exact MDH'| exact MDL'|].
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. apply rz_stop.
          set (xm := PST (x_p xc) S_NxtTag (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1))
                         (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)).
          rewrite EP1 in VERP, PLE, OUT.
          match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
            pose proof (ainv_stores E A1 m2 mf md1 _ _ PE0 AINV' MU WM WZ) as AINVm;
            assert (PIm : pinv E xm A1 mf); [| assert (HSm : hstep E x1 xm A1 A1 m2 mf)] end.
          { subst xm. apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
            all: rewrite ?ST1; try assumption. all: try exact (conj DELIM1 DELIM2). all: show_goal_heads. }
          { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                                 | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                                 | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
            w_in_zone_tac. left. unfold blk. lia. }
          rewrite EPx.
          eapply (G158 j xm A1 _ md1); [exact PIm| exact AINVm| exact MDF2| eapply hstep_trans; [exact HS2| exact HSm]
            | reflexivity| subst xm; psimp; exact AT1| reflexivity| subst xm; psimp; exact ECx| subst xm; psimp; exact EPx| exact HJ]. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0. { exfalso. unsign K0. clear - K0 PLT VERP Dlo Dhi CV; unfold pe_e, pe_N in *; lia. }
    clear K0. apply rz_stop.
    set (x0 := PST (x_p x) S_NxtTag (fupd (fupd (fupd (x_v x) Femptytag 0) Fattr 0) Fdostuff 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      pose proof (ainv_stores E A m mf md _ _ PE0 AINV MU WM WZ) as AINV0;
      assert (PI0' : pinv E x0 A mf); [| assert (HS0 : hstep E x x0 A A m mf)] end.
    { subst x0. apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      all: first [ left; reflexivity
                 | intros X; destruct X
                 | revert OUT; unfold oacost, oicost; cbn [x_va x_vi x_st x_p x_vv]; clear; intros; lia
                 | intros NZ; exact (AVSB NZ)
                 | show_goal_heads ]. }
    { eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                           | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                           | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
      w_in_zone_tac. left. unfold blk. lia. }
    eapply (NLOOP (Z.to_nat (pe_e E - x_p x)) x0 A _ md); [clear - PLT; rewrite Z2Nat.id by lia; reflexivity| exact PI0'| exact AINV0
      | apply md_frame_refl; [exact MDL| exact MDH]| exact HS0| reflexivity| subst x0; psimp; reflexivity| clear; apply Z.le_refl| exact PLT].
  Qed.
End S.
End V_PH968.

Module V_PHd1p.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_StartTag : handler_stmt S_StartTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    (* [comment removed for export] *)
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    (* [comment removed for export] *)
    eapply (KL (PST (x_p x) S_Match (fupd (fupd (fupd (x_v x) Fstate (st0 S_Match)) Fendtag 0) Fmatch TBL_starttag)
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    (* [comment removed for export] *)
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    (* [comment removed for export] *)
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    (* [comment removed for export] *)
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac. left. unfold blk. lia. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
        unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia. }
    (* [comment removed for export] *)
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
  Qed.
End S.
End V_PHd1p.

Module V_PHg4q.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit V_PH51p Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma PH_Attr : handler_stmt S_Attr.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    pose proof (DELIM1 ltac:(discriminate)) as DL0.
    assert (AV0 : x_v x Fattr_vsb = 0).
    { destruct (Z.eq_dec (x_v x Fattr_vsb) 0) as [X|X]; [exact X| exfalso; exact (AVSB X)]. }
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. rewrite DL0, sx32_zero. zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
    (* [comment removed for export] *)
    destruct ATTR as [AT0|(ATI & DOI & _)].
    - (* [comment removed for export] *)
      zstep. rewrite AT0. zstep. if_cases K2; zify_cond K2. { dead K2. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. rewrite AV0. zstep. if_cases K3; zify_cond K3. { dead K3. } clear K3.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x + 1) S_SkipAttribute (fupd (x_v x) Fstate (st0 S_SkipAttribute))
                      (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          destruct (vct_xmlname _); clear - PLT; lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) clear - VERP. lia.
      + (* [comment removed for export] *) clear - PLT. unfold pe_e in *. lia.
      + (* [comment removed for export] *) left. exact AT0.
    - (* [comment removed for export] *)
      zstep. rewrite ATI. unfold TBL_attr_include. (* [comment removed for export] *)
      zstep. if_cases K2; zify_cond K2. 2:{ dead K2. } clear K2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x) S_Match (fupd (fupd (x_v x) Fmatch TBL_attr_include) Fstate (st0 S_Match))
                      (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
          unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
      + (* [comment removed for export] *) intros _. exact (ARMED I).
      + (* [comment removed for export] *) right. split; [exact ATI|]. split; [exact DOI|]. left. reflexivity.
      + (* [comment removed for export] *) intros _ _. exact ATI.
      + (* [comment removed for export] *) intros _ _ HLT. refine (LOOKA eq_refl _ HLT). rewrite ATI. unfold TBL_attr_include. clear. lia.
  Qed.
End S.
End V_PHg4q.

Module V_PHtv2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r V_PKit V_PH51p Img0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Stgw7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Ma6xg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Lad4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Vct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Co10c OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH51p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_PH3d1.V_PHsgd.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Include : handler_stmt S_ESI_Include.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    (* [comment removed for export] *)
    assert (TAIL : forall (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a434 (x_p x) ra' t0' t1' t2' (Z_to_bv 64 (st0 S_TagError)) a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc])
      end.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (st0 S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
      2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MUc WMc WZ). }
      2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
      2:{ eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                               | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
          w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ. }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
        hide STK. hide_slow.
        call_fr (vep_error_inl 0x1a54c 0x1a58c (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
        1:{ right. split; reflexivity. }
        1:{ reflexivity. }
        1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
        1:{ exact TAG. }
        1:{ exact PADS. }
        1:{ exact (proj1 BASE). }
        1:{ exact HENV. }
        1:{ exact (proj1 PE0). }
        1:{ exact IMG. }
        1:{ exact VEPlo. }
        1:{ apply mod8_of_mod16. exact VEP16. }
        1:{ clear - VEPhi. lia. }
        1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
        1:{ exact CEIL. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
        1:{ exact MI. }
        clear STK. unhide_slow.
        zstep. zstep. zstep. apply rz_stop.
        eapply TAIL; [exact MU| exact WM| exact MI0| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact PC| exact POST]. }
    zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
    (* [comment removed for export] *)
    zstep. destruct B_et as [ET|ET]; rewrite ET, ?sx32_zero, ?sx32_one.
    2:{ (* [comment removed for export] *)
        zstep. if_cases K2; zify_cond K2. { dead K2. } clear K2.
        zstep. zstep. zstep. zstep.
        hide STK. hide_slow.
        call_fr (HVE (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
        1:{ reflexivity. }
        1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
        1:{ exact TAG. }
        1:{ exact PADS. }
        1:{ exact (proj1 BASE). }
        1:{ exact HENV. }
        1:{ exact (proj1 PE0). }
        1:{ exact IMG. }
        1:{ exact VEPlo. }
        1:{ apply mod8_of_mod16. exact VEP16. }
        1:{ clear - VEPhi. lia. }
        1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
        1:{ exact CEIL. }
        1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
        1:{ exact MI. }
        clear STK. unhide_slow.
        try match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
          replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]) end.
        zstep. zstep. zstep. apply rz_stop.
        eapply TAIL; [exact MU| exact WM| exact MI0| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact PC| exact POST]. }
    zstep. if_cases K2; zify_cond K2. 2:{ dead K2. } clear K2.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m) as MU2. pose proof (wmono_refl rsegs m) as WM2.
    assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (TBL_bom + 32) with TBL_attr_include by reflexivity.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply rz_stop.
    match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
      assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
        by (eapply (henv_stores E A _ _ md _ _ PE0 AINV MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENV])
    end.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (fupd (x_v x) Fattr TBL_attr_include) Fdostuff (vi_do_include VI0)) Fstate (st0 S_InTag))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ md).
    2:{ eapply (ainv_stores E A m _ md _ _ PE0 AINV MU WM WZ). }
    2:{ apply md_frame_refl; [exact MDL| exact MDH]. }
    2:{ eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
    (* [comment removed for export] *)
    2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia. }
    apply Build_pinv; psimp; pinv_close PE0 AINV MU WM WZ.
    (* [comment removed for export] *) { right; left; reflexivity. }
    (* [comment removed for export] *) right. split; [reflexivity| split; [reflexivity| left; exact I]].
  Qed.
End S.
End V_PHtv2.

Module V_veyvr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Img0 Img0 V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load_base | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.solve_load_sym ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)


Lemma sx32_small : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vep_do_comment_ok : vep_do_comment_stmt.
Proof.
  unfold vep_do_comment_stmt.
  intros VEP v tag q H lo. intros until m.
  intros A0 A1 VEPC TAG PADS HET EVC HENV HG IMG VLO V8 VHI ST LO CEIL SPH MI.
  rewrite A0, A1. unfold vep_do_comment_entry. unfold VEPERR_STACK in *.
  pose proof alloc_ceiling_val as ACV.
  (first [ dand3 HG as G16 GCE GHI | destruct HG as (G16 & GCE & GHI) ]). unfold HFRAME in GHI.
  assert (Evc : h_vc H = h_sp H + 1304) by reflexivity.
  assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity.
  assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity.
  assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.
  destruct HENV as [GLOB HOBJ].
  (first [ pose proof (GLOB) as dR_2; dand4 dR_2 as EBSS BSS CP [cnt CNT] | pose proof GLOB as (EBSS & BSS & CP & [cnt CNT]) ]). rewrite EBSS in BSS. cbn [vi_bss VI0 al_segs LayoutP0] in BSS.
  cbn [al_segs LayoutP0] in CP, CNT.
  (first [ pose proof (HOBJ) as dR_3; dand3 dR_3 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
  cbn [al_segs LayoutP0] in VC, WK. unfold vc_cells in VC. unfold wrk_cells in WK.
  (first [ dand4 IMG as _ _ GVSC _ | destruct IMG as (_ & _ & GVSC & _) ]). unfold GOT_vsc in GVSC.
  pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size v tag q TAG PADS) in VEPB.
  (first [ pose proof (PADS) as dR_7; dand7 dR_7 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
  unfold vep_cells in VEPC. rewrite EVC in VEPC.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KW; zify_cond KW. { exfalso. klia KW. } clear KW.
  zstep. rewrite (sx32_small (v Femptytag)) by (destruct HET; lia).
  zstep. if_cases KE; zify_cond KE.
  2:{ (* [comment removed for export] *)
    zstep. apply evt_done. unfold vep_error_post.
    do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
    split; [exact GLOB| exact HOBJ]. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 48%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
  release_frame FR ST (bv_unsigned sp).
  destruct (rw_cells_forget _ _ _ _ CNT) as [cnt' CNT']. cbn [cells_size csize Nat.add] in CNT'. clear CNT.
  apply evt_done. unfold vep_error_post.
  do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
  split.
  - eapply (glob_ok_intro LayoutP0); [exact EBSS| rewrite EBSS; cbn [vi_bss VI0 al_segs LayoutP0]; exact BSS | exact CP | exact CNT'].
  - eapply (hobj_ok_munch LayoutP0); [exact HOBJ| exact MU| exact WM|].
    intros a Ha. unfold h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
Qed.

End CEIL.
End V_veyvr.


Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_CommentESI : handler_stmt S_CommentESI.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (EVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity.
    assert (EVS : VEPERR_STACK = 48) by reflexivity.
    assert (SPR : 0 <= pe_sp E < 2^64) by (rewrite PSP; clear - CEIL LOP CV G3; unfold HFRAME in *; lia).
    (* [comment removed for export] *)
    assert (JOIN : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312); (pe_sp E - 48, pe_sp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m mc ->
      wmono rsegs m mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (x_v x) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) ->
      henv_ok LayoutP0 VI0 (pe_H E) mc -> stk rsegs mc (pe_lo E) (pe_sp E) ->
      realizes rsegs (mkCfg (loop_ms E 0x1a484 (x_p x) ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' t3' t4' t5' t6' mc) md) T).
    { intros until mc. intros MUc WMc MIc VEPCc FRc DBYc HENVc STKc. unfold loop_ms.
      clear VEPC FR DBY STK HENV MI.
      unfold vep_cells in VEPCc. rewrite STATE in VEPCc. unfold pframe in FRc.
      pose proof (ainv_stores E A m mc md _ _ PE0 AINV MUc WMc WZ) as AINVc.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] mc) as MU2. pose proof (wmono_refl rsegs mc) as WM2.
      assert (WZ2 : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                            [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH| exact MDL|].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply rz_stop.
      match goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mf _) _) _ =>
        assert (HENV2 : henv_ok LayoutP0 VI0 (pe_H E) mf)
          by (eapply (henv_stores E A _ _ md _ _ PE0 AINVc MU2 WM2 WZ2); [intros a Ha; cbn [outside]; clear - Ha VEPhi CV EVSC G2; lia| exact HENVc]);
        pose proof (ainv_stores E A m mf md _ _ PE0 AINV MUc WMc WZ) as AINV1
      end.
      (* [comment removed for export] *)
      set (xc := PST (x_p x) S_NxtTag (fupd (fupd (fupd (x_v x) Fesicmt LIT_arrow) Fesicmt_p LIT_arrow) Fstate (st0 S_NxtTag))
                     (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      match type of AINV1 with ainv _ ?mf _ =>
        assert (PIc : pinv E xc A mf); [| assert (HS1 : hstep E x xc A A m mf)] end.
      { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV MUc WMc WZ.
        (* [comment removed for export] *) right. split; [reflexivity| clear; lia]. }
      { eapply hstep_stores; [exact MUc | | eapply parse_window_mapped; [exact PE0| exact STKc| exact FRc]
                             | intros p0 X; refine (pst_blocks_same x _ _ _ _ _ p0 _ _ X); reflexivity
                             | intros a X; refine (parse_new_same E x _ a _ _ X); reflexivity ].
        w_in_zone_tac; [left; unfold blk; lia| do 5 right; exact Ha]. }
      (* [comment removed for export] *)
      eapply (mark_call HMC E xc A _ md T (x_p x) (x_p x) 1 0x1a4a8);
        [ exact PE | exact PIc | exact AINV1 | subst xc; cbn [x_p]; clear; lia | exact PLE | right; reflexivity | clear; lia | reflexivity
        | subst xc; cbn [x_st]; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (HS2 : hstep E x x1 A A1 m m2) by (eapply hstep_trans; [exact HS1| exact HS]).
      assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
      assert (EQ1 : x_tag x1 = x_tag x /\ x_q x1 = x_q x /\ x_va x1 = x_va x /\ x_vi x1 = x_vi x) by (rewrite EX1; subst xc; repeat split; reflexivity).
      clear - HMC PE ST PLT KL KX PI1 AINV' MDF HS2 VK VERP1 LM1 OP1 ST1 EV1 EP1 EQ1.
      pose proof (as_lazy_nil _ _ _ AINV') as [MDL' MDH'].
      world_open PE PI1 AINV'. rewrite <- EP1.
      (* [comment removed for export] *)
      unfold loop_ms.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      apply rz_go; [exact MDH'| exact MDL'|].
      zstep. zstep. zstep. zstep.
      apply rz_stop.
      eapply (KL (PST (x_p x1) S_NxtTag
                      (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1))
                      (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ md1).
      2:{ eapply (ainv_stores E A1 m2 _ md1 _ _ PE0 AINV' MU WM WZ). }
      2:{ exact MDF. }
      2:{ eapply hstep_trans; [exact HS2|].
          eapply hstep_stores; [exact MU | | eapply parse_window_mapped; [exact PE0| exact STK| exact FR]
                               | intros p0 X; refine (pst_blocks_same x1 _ _ _ _ _ p0 _ _ X); reflexivity
                               | intros a X; refine (parse_new_same E x1 _ a _ _ X); reflexivity ].
          w_in_zone_tac. left. unfold blk. lia. }
      (* [comment removed for export] *)
      2:{ psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST, EP1. lia. }
      apply Build_pinv; psimp; pinv_close PE0 AINV' MU WM WZ.
    }
    (* [comment removed for export] *)
    apply rz_go; [exact MDH| exact MDL|].
    (* [comment removed for export] *)
    zstep. destruct B_rm as [RM|RM]; rewrite RM, ?sx32_zero, ?sx32_one.
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1. 2:{ dead K1. } clear K1.
      apply rz_stop. eapply JOIN; [exact MU| exact WM| exact MI| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact HENV| exact STK].
    - (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1. { dead K1. } clear K1.
      hide STK. hide_slow.
      call_fr (vep_error_inl 0x1a444 0x1a484 (pe_VEP E) (x_v x) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by idtac.
      1:{ left. split; reflexivity. }
      1:{ reflexivity. }
      1:{ unfold vep_cells. rewrite STATE. exact VEPC. }
      1:{ exact TAG. }
      1:{ exact PADS. }
      1:{ exact (proj1 BASE). }
      1:{ exact HENV. }
      1:{ exact (proj1 PE0). }
      1:{ exact IMG. }
      1:{ exact VEPlo. }
      1:{ apply mod8_of_mod16. exact VEP16. }
      1:{ clear - VEPhi. lia. }
      1:{ unhide STK. rewrite unsigned_lit by exact SPR. exact STK. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite EVS, PSP. clear - LOP. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by exact SPR. rewrite PSP. clear. lia. }
      1:{ exact MI. }
      clear STK. unhide_slow.
      apply rz_stop.
      eapply JOIN; [exact MU| exact WM| exact MI0| unfold vep_cells; rewrite STATE; exact VEPC| unfold pframe; exact FR| exact DBY| exact PC| exact POST].
  Qed.
End S.
