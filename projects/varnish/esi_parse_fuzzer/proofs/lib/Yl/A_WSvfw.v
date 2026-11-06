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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac icall_consts_in H ::= unfold leaf_post, WSEMU_STACK, WSASSERT_STACK, WSMARK_STACK, h_ws, h_wsbuf in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI"] Lemma ws_emu_ok : ws_emu_stmt.
  Proof.
    unfold ws_emu_stmt.
    intros H wr we lo. intros until v. intros A0 WSC LID WSS WEC HSH HG CE ST LO CEIL MI.
    rewrite A0. unfold ws_emu_entry, WSEMU_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_1; dand3 dR_1 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    (first [ pose proof ((hshadow_shadowed LPA H v HSH HG)) as dR_2; dand10 dR_2 as _ _ _ _ _ _ SHW _ _ SHWB | destruct (hshadow_shadowed LPA H v HSH HG) as (_ & _ & _ & _ & _ & _ & SHW & _ & _ & SHWB) ]).
    (first [ dand8 SHW as P NP SHP PAL P0 PLE PGE PCE | destruct SHW as (P & NP & SHP & PAL & P0 & PLE & PGE & PCE) ]). fold_cl_segs.
    (first [ dand8 SHWB as Q NQ SHQ QAL Q0 QLE QGE QCE | destruct SHWB as (Q & NQ & SHQ & QAL & Q0 & QLE & QGE & QCE) ]). fold_cl_segs.
    unfold h_ws, h_wsbuf in *.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB. rewrite SHMAX_val in SHPB.
    pose proof (shpat_sh_boundL (Clg:=Clg) Q NQ ltac:(lia) ltac:(lia) ltac:(lia)) as SHQB. rewrite SHMAX_val in SHQB.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (rw_cells_bound _ _ _ _ WSC) as SB. rewrite (ws_cells_size wr LID) in SB.
    unfold ws_cells in WSC. rewrite WSS in WSC. unfold wsemu_cells in WEC.
    pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    carve_frame 16%nat ST.
    zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. shadow_chk0 SHP 8.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K0; zify_cond K0. { dead K0. } clear K0.
    (* [comment removed for export] *)
    shadow_chk SHQ 4 12.
    zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1. { exfalso. revert K1. vm_compute. congruence. } clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    try replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    apply evt_done; hnf.
    repeat (lazymatch goal with |- ex _ => eexists | |- word => exact (Z_to_bv 64 0) end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma WS_Assert_ok : WS_Assert_stmt.
  Proof.
    unfold WS_Assert_stmt.
    intros H E lo. intros until v. intros A0 WSX GLOB HSH HG CE ST LO CEIL MI.
    rewrite A0. unfold WS_Assert_entry, WSASSERT_STACK, WSEMU_STACK in *.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HG) as dR_5; dand3 dR_5 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts. (* [comment removed for export] *) pose proof G2 as G2x__; dand17 G2x__ as G2_01 G2_02 G2_03 G2_04 G2_05 G2_06 G2_07 G2_08 G2_09 G2_10 G2_11 G2_12 G2_13 G2_14 G2_15 G2_16 G2_17. hide G2.
    pose proof (hff_al8 H 2976 HG eq_refl) as AL1. pose proof (hff_al8 H 3152 HG eq_refl) as AL2.
    pose proof (hff_al8 H 1536 HG eq_refl) as AL3.
    (first [ pose proof (HSH) as dR_6; dand10 dR_6 as _ SHC _ _ _ _ SHW _ _ SHB | pose proof HSH as (_ & SHC & _ & _ & _ & _ & SHW & _ & _ & SHB) ]). fold_cl_segs.
    (first [ pose proof ((shadowed_bss_cp v (proj1 CE))) as dR_7; dand8 dR_7 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_cp v (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_cp VIA] in GLE, GGE.
    unfold h_ws, h_wsbuf, h_cp in SHC, SHW, SHB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2976) 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWR. rewrite SHMAX_val in SHWR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3152) 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as SHBR. rewrite SHMAX_val in SHBR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 1536) 752 ltac:(lia) ltac:(lia) ltac:(lia)) as SHCR. rewrite SHMAX_val in SHCR.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC.
    pose proof (got_cp_cell v (proj1 CE)) as GOTC. unfold GOTA_cp in GOTC. cbn [vi_bss_cp VIA] in GOTC.
    (first [ pose proof (GLOB) as dR_8; dand4 dR_8 as _ BSS CP _ | pose proof GLOB as (_ & BSS & CP & _) ]). fold_cl_segs. cbn [vi_bss_cp VIA] in BSS.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] v) as MU.
    pose proof (wmono_refl rsegs v) as WM.
    open_map_cells MC.
    unfold h_ws, h_wsbuf, h_cp in *.
    destruct E as [[[A wa] vep]|].
    - (* [comment removed for export] *)
      (first [ dand7 WSX as WS1 SHDA WAL WLO WHI VLO VHI | destruct WSX as (WS1 & SHDA & WAL & WLO & WHI & VLO & VHI) ]). unfold kHighMemBeg in WLO, VLO. all_app_facts.
      (first [ dex2 WS1 as id pad; dand7 WS1 as IDOK PADL WSC WEC LWA WAC LVEP | dand9 WS1 as id pad IDOK PADL WSC WEC LWA WAC LVEP | destruct WS1 as (id & pad & IDOK & PADL & WSC & WEC & LWA & WAC & LVEP) ]). fold_cl_segs.
      (first [ dand8 SHDA as PA NA SHA AAL PA0 ALE AGE ACE | destruct SHDA as (PA & NA & SHA & AAL & PA0 & ALE & AGE & ACE) ]). fold_cl_segs.
      pose proof (shpat_sh_boundL (Clg:=Clg) PA NA ltac:(lia) ltac:(lia) ltac:(lia)) as SHAR. rewrite SHMAX_val in SHAR.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      pose proof (rw_cells_bound _ _ _ _ WSC) as SB. rewrite (ws_cells_size (ws_rec_of H id) IDL) in SB.
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS1 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold wsalloc_cells, wsalloc_WS1 in WAC. cbn [wa_off wa_len wa_ptr wa_next wa_prev] in WAC.
      unfold h_ws, h_wsbuf in WSC, WEC, WAC, SB.
      carve_frame 64%nat ST.
      (* [comment removed for export] *)
      do 8 zstep.
      (* [comment removed for export] *)
      zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      shadow_chk SHW 4 11.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8.
      zstep. zstep. kdead. zstep. zstep. if_cases K; zify_cond K. { paok K HG. } clear K.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8.
      zstep. zstep. kdead. zstep. zstep. if_cases K; zify_cond K. { paok K HG. } clear K.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (ws_emu_ok H (ws_rec_of H id) (wsemu_WS1 wa) lo)
        by (try rewrite unsigned_lit by lia; unfold WSEMU_STACK, h_ws, h_wsbuf, kHighMemBeg;
            first [ reflexivity
                  | exact WSC
                  | exact WEC
                  | (cbn [ws_id ws_rec_of]; exact IDL)
                  | (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
                  | exact HG
                  | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                  | exact ST
                  | assumption
                  | lia ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      shadow_rechk0 SHW (h_ff H + 2984) 8. shadow_rechk0 SHW (h_ff H + 3008) 8.
      (* [comment removed for export] *)
      zstep. zstep. kdead. zstep. zstep. kdead. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHB 4 13. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHB 8. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      do 8 zstep. rewrite (shr3_div8 (h_ff H + 2992)).
      (* [comment removed for export] *)
      zstep. shadow_chk SHA 4 7.
      (* [comment removed for export] *)
      zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHA 4 28. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHA 8. shadow_rechk0 SHW (h_ff H + 2992) 8.
      (* [comment removed for export] *)
      zstep. zstep. kdead. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHA 4 28. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHA 8. zstep. zstep. kdead. zstep.
      (* [comment removed for export] *)
      shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6191712 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC 1 15. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead.
      (* [comment removed for export] *)
      do 9 zstep.
      try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold leaf_post.
      hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
    - (* [comment removed for export] *)
      (first [ dex1 WSX as id; dand3 WSX as IDOK WSC WEC | dand4 WSX as id IDOK WSC WEC | destruct WSX as (id & IDOK & WSC & WEC) ]). fold_cl_segs.
      assert (IDL : length id = 4%nat) by (destruct IDOK as [-> | ->]; reflexivity).
      pose proof (rw_cells_bound _ _ _ _ WSC) as SB. rewrite (ws_cells_size (ws_rec_of H id) IDL) in SB.
      unfold ws_cells, ws_rec_of in WSC. cbn [ws_id ws_s ws_f ws_r ws_e] in WSC.
      unfold wsemu_cells, wsemu_WS0 in WEC. cbn [we_len we_ws we_first we_last] in WEC.
      unfold h_ws, h_wsbuf in WSC, WEC, SB.
      carve_frame 64%nat ST.
      (* [comment removed for export] *)
      do 8 zstep.
      (* [comment removed for export] *)
      zstep. kdead.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      shadow_chk SHW 4 11.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8.
      zstep. zstep. kdead. zstep. zstep. if_cases K; zify_cond K. { paok K HG. } clear K.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8.
      zstep. zstep. kdead. zstep. zstep. if_cases K; zify_cond K. { paok K HG. } clear K.
      (* [comment removed for export] *)
      zstep. zstep.
      icall (ws_emu_ok H (ws_rec_of H id) (wsemu_WS0 (h_ff H + 3152)) lo)
        by (try rewrite unsigned_lit by lia; unfold WSEMU_STACK, h_ws, h_wsbuf, kHighMemBeg;
            first [ reflexivity
                  | exact WSC
                  | exact WEC
                  | (cbn [ws_id ws_rec_of]; exact IDL)
                  | (eapply hshadow_munch; [exact HSH| exact MU| exact HG| intros x__ Hx__; change (HFSIZE / 8) with 1024 in Hx__; cbn; lia])
                  | exact HG
                  | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                  | exact ST
                  | assumption
                  | lia ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      shadow_rechk0 SHW (h_ff H + 2984) 8. shadow_rechk0 SHW (h_ff H + 3008) 8.
      (* [comment removed for export] *)
      zstep. zstep. kdead. zstep. zstep. kdead. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk SHB 4 13. zstep. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHB 8. zstep. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHW 8. zstep. zstep. kdead2.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      shadow_addr_at SHG 6191712 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K; zify_cond K;
        [ first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K; clear K; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk SHC 1 15. zstep. (* [comment removed for export] *) match goal with |- context [ zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn ?zk (repeat (Z_to_bv 8 0) ?zn))))) ] => replace (zext 64 (bv_extract 0 8 (le_bytes_to_word (firstn 1 (skipn zk (repeat (Z_to_bv 8 0) zn)))))) with (Z_to_bv 64 0) by (vm_compute; reflexivity) end. zstep. zstep. kdead.
      (* [comment removed for export] *)
      do 9 zstep.
      try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
      release_frame FR ST (bv_unsigned sp).
      apply evt_done. unfold leaf_post.
      hot_eexists_k16. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mark_close H WSC1 WEC MU WM ST :=
    let WSC := fresh "WSC" in
    lazymatch type of WSC1 with rw_cells _ ?mx ?b (?c0 :: ?c1 :: ?c2 :: ?rest) =>
      pose proof (rw_cells_merge rsegs mx b [c0] [c1; c2] rest WSC1) as WSC end;
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in WSC; clear WSC1;
    apply evt_done; unfold WS_MarkOverflow_post;
    hot_eexists_k16; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|];
    apply (ws0_obj_intro LPA H _ ws_id_Req); [right; reflexivity| | exact WEC];
    unfold ws_cells, ws_rec_of, ws_id_Req; cbn [ws_id ws_s ws_f ws_r ws_e]; fold_cl_segs; unfold h_ws, h_wsbuf; exact WSC.

  (* [comment removed for export] *)
End S.
