(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_World A_Img A_Cocsh A_Tac A_vei6d.

Module A_vej1r.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World A_Img A_Cocsh A_Tac A_vei6d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Lemma sx32_small : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma vep_do_comment_ok : vep_do_comment_stmt.
  Proof.
    unfold vep_do_comment_stmt.
    intros VEP vv tag q H lo. intros until v. intros A0 A1 VEPC TAG PADS HET EVC GLOB HOBJ HSH HG CE SHD VLO V8 VHI VFR ST LO CEIL MI.
    rewrite A0, A1. unfold vep_do_comment_entry, VEPERR_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3, VLO, VFR. all_app_facts.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as SHV _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHV & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHV, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ dand8 SHD as PV NV SHP PAL P0 PLE PGE PCE | destruct SHD as (PV & NV & SHP & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (shpat_sh_boundL (Clg:=Clg) PV NV ltac:(lia) ltac:(lia) ltac:(lia)) as SHPR. rewrite SHMAX_val in SHPR.
    (first [ pose proof ((shadowed_bss_vsc v (proj1 CE))) as dR_4; dand8 dR_4 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_vsc v (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (got_vsc_cell v (proj1 CE)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (GLOB) as dR_5; dand4 dR_5 as BSSV BSS CP [cnt CNT] | pose proof GLOB as (BSSV & BSS & CP & [cnt CNT]) ]). fold_cl_segs. cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS. unfold h_vsc, h_cp in BSSV, BSS, CP, CNT.
    (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size vv tag q TAG PADS) in VEPB; change (Z.of_nat 312) with 312 in VEPB.
    (first [ pose proof (PADS) as dR_9; dand7 dR_9 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (h_ff H + 32 + 1304, h_ff H + 32 + 1320)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. first [if_true | if_false].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk SHP 4 14.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small (vv Femptytag)) by (destruct HET; lia).
    zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep.
      try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      replace (h_ff H + 1336) with (h_ff H + 32 + 1304) in CNT by lia.
      apply evt_done. unfold vep_error_post, VEPERR_STACK. unfold h_vsc.
      hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|split; [|exact ST]].
      - eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [exact BSSV| exact BSS| exact CP| exact CNT].
      - eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|].
        intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. lia. }
    (* [comment removed for export] *)
    vep_error_core SHG SHV SHP SHc SHw.
    (* [comment removed for export] *)
    do 8 zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    vslb_tail ST sp.
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
    replace (h_ff H + 1336) with (h_ff H + 32 + 1304) in CNT' by lia.
    apply evt_done. unfold vep_error_post, VEPERR_STACK. unfold h_vsc.
    hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|split; [|exact ST]].
    - eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [exact BSSV| exact BSS| exact CP| exact CNT'].
    - eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|].
      intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
  Qed.
End S.
End A_vej1r.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vexn5.A_vej1r.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
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
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VLO; @SZ; @SR; @LO; @G2; @TAG; @LP1; @LR1; @LP2; @LR2; @P36; @P124; @P140; @P196; @P236; @P268; @P308; @P0; @G0; @CEIL; @VEPB; @PGE; @PCE; @VFR; @H0; @ACV; @H4; @Ha; @G3; @G1; @Hx; @H1; @H5; @H6; @H11; @H45; @PLE; @GLE; @GGE; @GCE; @KU; @KE; @H35; @KN; @KR; @H16])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac vdr_err_tail :=
  lazymatch goal with FR : rw_cells _ ?mx (bv_unsigned ?sp + -16) _, ST : stk _ ?mx ?lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    release_frame FR ST (bv_unsigned sp);
    vslb_tail ST sp
  end;
  lazymatch goal with CNT : rw_cells _ ?mx (h_ff ?H + 1336) _, MU : munch _ _ _, WM : wmono _ _ _, ST : stk _ ?mx _ _,
                      VEPC : rw_cells _ ?mx ?VEP (C4 (Z_to_bv 64 VEP_MAGIC) :: _), HRM : bool01 (?vv Fremove), HOBJ : hobj_ok _ _ _ _,
                      EVC : ?vv Fvc = h_vc ?H |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    let c := fresh "cnt'" in let C := fresh "CNT'" in
    destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C; clear CNT;
    replace (h_ff H + 1336) with (h_ff H + 32 + 1304) in C by lia;
    replace (h_ff H + 2608) with (h_vc H) in VEPC by reflexivity; rewrite <- EVC in VEPC;
    apply evt_done; unfold vep_do_remove_post, VEPERR_STACK; unfold h_vsc;
    hot_eexists_k16; exists (vv Fremove);
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [|split; [| split; [exact ST| split; [exact HRM|
      unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC]]]];
    [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [eassumption| eassumption| eassumption| exact C]
    | eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
      intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; lia ]
  end.

(* [comment removed for export] *)
Ltac vdr_store_tail SHP :=
  lazymatch goal with VEPC : rw_cells _ _ ?VEP (C4 (Z_to_bv 64 VEP_MAGIC) :: _) |- _ =>
    shadow_rechk SHP (VEP + 80) 4 13;
    shadow_rechk_gen SHP (VEP + 92) 4 12 1
  end;
  zstep; zstep; zstep; zstep;
  lazymatch goal with FR : rw_cells _ ?mx (bv_unsigned ?sp + -16) _, ST : stk _ ?mx ?lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    release_frame FR ST (bv_unsigned sp)
  end;
  zstep;
  lazymatch goal with CNT : rw_cells _ ?mx (h_ff ?H + 1336) _, MU : munch _ _ _, WM : wmono _ _ _, ST : stk _ ?mx _ _,
                      VEPC : rw_cells _ ?mx ?VEP (C4 (Z_to_bv 64 VEP_MAGIC) :: _), HOBJ : hobj_ok _ _ _ _,
                      EVC : ?vv Fvc = h_vc ?H |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of VEPC with context [C4 (Z_to_bv 64 ?rm) :: C8 (Z_to_bv 64 (vv Fo_wait)) :: _] =>
    replace (h_ff H + 1336) with (h_ff H + 32 + 1304) in CNT by lia;
    replace (h_ff H + 2608) with (h_vc H) in VEPC by reflexivity; rewrite <- EVC in VEPC;
    apply evt_done; unfold vep_do_remove_post, VEPERR_STACK; unfold h_vsc;
    hot_eexists_k16; exists rm;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|];
    split; [| split; [| split; [exact ST| split; [| unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; exact VEPC]]]];
    [ eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [eassumption| eassumption| eassumption| exact CNT]
    | eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|];
      intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; lia
    | unfold bool01;
      match goal with
      | |- context [Z.b2z (?x <? ?y)] => destruct (Z.ltb_spec x y); cbn; lia
      | |- context [Z.b2z (?x =? ?y)] => destruct (Z.eqb_spec x y); cbn; lia
      end ]
    end
  end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma vep_do_remove_ok : vep_do_remove_stmt.
  Proof.
    unfold vep_do_remove_stmt.
    intros VEP vv tag q H lo. intros until v. intros A0 A1 VEPC TAG PADS HET HEN HRM EVC GLOB HOBJ HSH HG CE SHD VLO V8 VHI VFR ST LO CEIL MI.
    rewrite A0, A1. unfold vep_do_remove_entry, VEPERR_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3, VLO, VFR. all_app_facts.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as SHV _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHV & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHV, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ dand8 SHD as PV NV SHP PAL P0 PLE PGE PCE | destruct SHD as (PV & NV & SHP & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (shpat_sh_boundL (Clg:=Clg) PV NV ltac:(lia) ltac:(lia) ltac:(lia)) as SHPR. rewrite SHMAX_val in SHPR.
    (first [ pose proof ((shadowed_bss_vsc v (proj1 CE))) as dR_4; dand8 dR_4 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_vsc v (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (got_vsc_cell v (proj1 CE)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (GLOB) as dR_5; dand4 dR_5 as BSSV BSS CP [cnt CNT] | pose proof GLOB as (BSSV & BSS & CP & [cnt CNT]) ]). fold_cl_segs. cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS. unfold h_vsc, h_cp in BSSV, BSS, CP, CNT.
    (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size vv tag q TAG PADS) in VEPB; change (Z.of_nat 312) with 312 in VEPB.
    (first [ pose proof (PADS) as dR_9; dand7 dR_9 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (h_ff H + 32 + 1304, h_ff H + 32 + 1320); (VEP + 92, VEP + 96)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. first [if_true | if_false].
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk SHP 4 14.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small (vv Femptytag)) by (destruct HET; lia).
    zstep. if_cases KE; zify_cond KE.
    all: cycle 1.
    - (* [comment removed for export] *)
      vep_error_core SHG SHV SHP SHc SHw.
      (* [comment removed for export] *)
      do 8 zstep.
      vdr_err_tail.
    - (* [comment removed for export] *)
      zstep. shadow_chk SHP 4 15.
      (* [comment removed for export] *)
      zstep. shadow_chk_gen SHP 4 5 1.
      rewrite (sx32_small (vv Fremove)) by (destruct HRM; lia).
      (* [comment removed for export] *)
      zstep. rewrite (sx32_small (vv Fendtag)) by (destruct HEN; lia).
      zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        zstep. if_cases KN; zify_cond KN.
        * (* [comment removed for export] *) vdr_store_tail SHP.
        * (* [comment removed for export] *)
          vep_error_core SHG SHV SHP SHc SHw. do 5 zstep. do 4 zstep. vdr_err_tail.
      + (* [comment removed for export] *)
        zstep. if_cases KN; zify_cond KN.
        * (* [comment removed for export] *) vdr_store_tail SHP.
        * (* [comment removed for export] *)
          vep_error_core SHG SHV SHP SHc SHw. do 5 zstep. do 4 zstep. vdr_err_tail.
  Qed.
End S.
