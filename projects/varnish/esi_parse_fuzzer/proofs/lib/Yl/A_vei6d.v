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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac vep_error_core SHG SHV SHP SHc SHw :=
  zstep; zstep;
  zstep; zstep;
  shadow_addr_at SHG 6191680 8;
  match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
    let e' := eval vm_compute in e in change e with e' in RD end;
  zstep;
  (let K0 := fresh "K0" in
   zstep; if_cases K0; zify_cond K0;
    [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
    | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ]);
  zstep; zstep; shadow_chk0 SHV 8; zstep; zstep; zstep;
  zstep; shadow_chk0 SHP 8; zstep;
  zstep; shadow_chk0 SHc 8; zstep;
  zstep; shadow_chk0 SHw 8;
  zstep; shadow_chk0 SHP 8; zstep; zstep.

(* [comment removed for export] *)
Ltac vslb_tail ST sp :=
  zstep;
  carve_frame 48%nat ST;
  do 8 zstep;
  try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
  lazymatch goal with FR : rw_cells _ ?mx (bv_unsigned sp + -48) _, STx : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    release_frame FR STx (bv_unsigned sp) end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma vep_error_ok : vep_error_stmt.
  Proof.
    unfold vep_error_stmt.
    intros VEP vv tag q H lo. intros until v. intros A0 VEPC TAG PADS EVC GLOB HOBJ HSH HG CE SHD VLO V8 VHI VFR ST LO CEIL MI.
    rewrite A0. unfold vep_error_entry, VEPERR_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3, VLO, VFR. all_app_facts.
    pose proof (hff_al8 H 32 HG eq_refl) as ALv. pose proof (hff_al8 H 2608 HG eq_refl) as ALc. pose proof (hff_al8 H 2720 HG eq_refl) as ALw.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    (first [ pose proof (HSH) as dR_2; dand10 dR_2 as SHV _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHV & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHV, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    (first [ dand8 SHD as PV NV SHP PAL P0 PLE PGE PCE | destruct SHD as (PV & NV & SHP & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    pose proof (shpat_sh_boundL (Clg:=Clg) PV NV ltac:(lia) ltac:(lia) ltac:(lia)) as SHPR. rewrite SHMAX_val in SHPR.
    (first [ pose proof ((shadowed_bss_vsc v (proj1 CE))) as dR_4; dand8 dR_4 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_vsc v (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (* [comment removed for export] *)
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (got_vsc_cell v (proj1 CE)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (GLOB) as dR_5; dand4 dR_5 as BSSV BSS CP [cnt CNT] | pose proof GLOB as (BSSV & BSS & CP & [cnt CNT]) ]). fold_cl_segs. cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS. unfold h_vsc, h_cp in BSSV, BSS, CP, CNT.
    (first [ pose proof (HOBJ) as dR_6; dand3 dR_6 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    replace (h_ff H + 32 + 1304) with (h_ff H + 1336) in CNT by lia.   (* [comment removed for export] *)
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size vv tag q TAG PADS) in VEPB.
    (first [ pose proof (PADS) as dR_9; dand7 dR_9 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (h_ff H + 32 + 1304, h_ff H + 32 + 1320)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    shadow_addr_at SHG 6191680 8.
    match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
      let e' := eval vm_compute in e in change e with e' in RD end.
    zstep. zstep; if_cases K0; zify_cond K0;
      [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
      | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
    (* [comment removed for export] *)
    zstep. zstep. shadow_chk0 SHV 8. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHP 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHc 8. zstep.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHw 8.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHP 8. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    (* [comment removed for export] *)
    vslb_tail ST sp.
    (* [comment removed for export] *)
    lazymatch goal with X : rw_cells rsegs ?mx (h_ff H + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
    replace (h_ff H + 1336) with (h_ff H + 32 + 1304) in CNT' by lia.
    apply evt_done. unfold vep_error_post, VEPERR_STACK. unfold h_vsc.
    do 16 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|split; [|exact ST]].
    - eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [exact BSSV| exact BSS| exact CP| exact CNT'].
    - eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|].
      intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
  Qed.
End S.
