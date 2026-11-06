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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.

Module A_PHkg6.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vei6d A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vei6d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Definition errinl_post (ret : Z) (E : penv) (A : AS) (gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists a0 a1 a2 a3 a4 m',
      ms' = MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (pe_fp E)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 ret) fc None m' (seg_rom rsegs)
      /\ munch [(pe_fp E - 48, pe_fp E); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ henv_ok LPA VIA (pe_H E) A m' /\ stk rsegs m' lo (pe_fp E).

  Lemma errinl_spec :
    forall (site ret : Z) (E : penv) (A : AS) (vv : vep) (tag : list byte) (q : vep_pads) (j0 j8 : word) (lo : Z) (zsV : list byte),
    forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      ((site = 0x8c324 /\ ret = 0x8c3ec /\ a2 = Z_to_bv 64 (pe_VEP E + 24)) \/ (site = 0x8c608 /\ ret = 0x8c6d4)) ->
      penv_ok E ->
      rw_cells rsegs m (pe_VEP E) (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
      vv Fvc = h_vc (pe_H E) -> henv_ok LPA VIA (pe_H E) A m -> cenv m ->
      rw_cells rsegs m (pe_fp E) (pframe E j0 j8) ->
      bytes_at rsegs m (sh (pe_VEP E)) zsV -> zsV = repeat (Z_to_bv 8 0) 39 ->
      17594333495296 <= pe_VEP E -> pe_VEP E mod 16 = 0 -> pe_VEP E + 312 <= alloc_ceiling ->
      (h_ff (pe_H E) + 8192 <= pe_VEP E - 16 \/ pe_VEP E + 312 <= h_ff (pe_H E)) ->
      stk rsegs m lo (pe_fp E) -> lo + 48 <= pe_fp E -> alloc_ceiling <= lo ->
      mem_inv rsegs m ->
      evt rsegs (errinl_post ret E A gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
        (MS (mkR ra (Z_to_bv 64 (pe_fp E)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 site) fc None m (seg_rom rsegs)).
  Proof.
    intros site ret E A vv tag q j0 j8 lo zsV. intros until m.
    intros SITE PE VEPC TAG PADS EVC HENV CE FR SHV0 EzsV VLO V16 VHI DJfV ST LO CEIL MI.
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (PE) as dR_1; dand7 dR_1 as HG _ _ CEIL0 LOP SPH _ | pose proof PE as (HG & _ & _ & CEIL0 & LOP & SPH & _) ]). rewrite PARSE_STACK_val in LOP. unfold pe_fp, PARSE_FRAME in *.
    (first [ pose proof (HG) as dR_2; dand3 dR_2 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts.
    pose proof (hff_al8 (pe_H E) 32 HG eq_refl) as ALv. pose proof (hff_al8 (pe_H E) 2608 HG eq_refl) as ALc. pose proof (hff_al8 (pe_H E) 2720 HG eq_refl) as ALw.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ dand4 HENV as HFR GLOB HOBJ HSH | destruct HENV as (HFR & GLOB & HOBJ & HSH) ]).
    (* [comment removed for export] *)
    (first [ pose proof (HSH) as dR_4; dand10 dR_4 as SHV _ _ _ SHc SHw _ _ _ _ | pose proof HSH as (SHV & _ & _ & _ & SHc & SHw & _ & _ & _ & _) ]). fold_cl_segs. unfold h_vsc, h_vc, h_wrk in SHV, SHc, SHw.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff (pe_H E) + 32) 1368 ltac:(lia) ltac:(lia) ltac:(lia)) as SHVR. rewrite SHMAX_val in SHVR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff (pe_H E) + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHcR. rewrite SHMAX_val in SHcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff (pe_H E) + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwR. rewrite SHMAX_val in SHwR.
    pose proof (sh_boundL (Clg:=Clg) (pe_VEP E) 312 ltac:(lia) ltac:(lia) VHI) as SHVB. rewrite SHMAX_val in SHVB. change ((312 + 7) / 8) with 39 in SHVB.
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity).
    (first [ pose proof ((shadowed_bss_vsc m (proj1 CE))) as dR_5; dand8 dR_5 as PG NG SHG GAL G0 GLE GGE GCE | destruct (shadowed_bss_vsc m (proj1 CE)) as (PG & NG & SHG & GAL & G0 & GLE & GGE & GCE) ]). fold_cl_segs.
    cbn [vi_bss_vsc VIA] in GLE, GGE.
    pose proof (shpat_sh_boundL (Clg:=Clg) PG NG ltac:(lia) ltac:(lia) ltac:(lia)) as SHGR. rewrite SHMAX_val in SHGR.
    (* [comment removed for export] *)
    pose proof (got_vsc_cell m (proj1 CE)) as GOTV. unfold GOTA_vsc in GOTV. cbn [vi_bss_vsc VIA] in GOTV.
    (first [ pose proof (GLOB) as dR_6; dand4 dR_6 as BSSV BSS CP [cnt CNT] | pose proof GLOB as (BSSV & BSS & CP & [cnt CNT]) ]). fold_cl_segs. cbn [vi_bss_vsc vi_bss_cp VIA] in BSSV, BSS. unfold h_vsc, h_cp in BSSV, BSS, CP, CNT.
    (first [ pose proof (HOBJ) as dR_7; dand3 dR_7 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
    replace (h_ff (pe_H E) + 32 + 1304) with (h_ff (pe_H E) + 1336) in CNT by lia.
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB. rewrite (vep_cells_size vv tag q TAG PADS) in VEPB.
    (first [ pose proof (PADS) as dR_10; dand7 dR_10 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]).
    unfold vep_cells in VEPC. rewrite EVC in VEPC. unfold h_vc in VEPC.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB. rewrite pframe_size in FRB. unfold pframe in FR. cbv zeta in FR.
    pose proof (munch_refl [(pe_sp E - 304 - 48, pe_sp E - 304); (h_ff (pe_H E) + 32 + 1304, h_ff (pe_H E) + 32 + 1320)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    destruct SITE as [(-> & -> & ->)|(-> & ->)].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. zstep.
      shadow_addr_at SHG 6191680 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. shadow_addr SHV 8. zstep. zstep.
      zstep; if_cases K1; zify_cond K1;
        [ first [ shadow_fast K1; clear K1; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K1; clear K1; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      (* [comment removed for export] *)
      vchk SHV0 EzsV 8 0. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
      (* [comment removed for export] *)
      vchk SHV0 EzsV 8 0. zstep. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. carve_frame 48%nat ST. replace (pe_sp E + -304 + -48) with (pe_sp E + -352) in * by (clear; lia).
      do 8 zstep.
      lazymatch goal with FRs : rw_cells _ ?mx (pe_sp E + -352) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame FRs ST (pe_sp E + -304) end.
      replace (pe_sp E + -304) with (pe_sp E - 304) in * by (clear; lia).
      lazymatch goal with X : rw_cells rsegs ?mx (h_ff (pe_H E) + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
      replace (h_ff (pe_H E) + 1336) with (h_ff (pe_H E) + 32 + 1304) in CNT' by lia.
      replace (pe_sp E + -352) with (pe_sp E - 304 - 48) in MU by (clear; lia).
      apply evt_done. unfold errinl_post. unfold h_vsc, pe_fp, PARSE_FRAME.
      do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
      split; [exact HFR|]. split; [| split].
      + eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [exact BSSV| exact BSS| exact CP| exact CNT'].
      + eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|].
        intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
      + eapply hshadow_munch; [exact HSH| exact MU| exact HG|].
        intros a Ha. unfold HFSIZE in Ha. change (8192 / 8) with 1024 in Ha. cbn [outside].
        pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFB. rewrite SHMAX_val in SHFB. lia.
    - (* [comment removed for export] *)
      zstep. zstep.
      zstep. zstep.
      shadow_addr_at SHG 6191680 8.
      match goal with RD : ov_read_bytes _ _ (Z_to_bv 64 ?e) 1 = Some _ |- _ =>
        let e' := eval vm_compute in e in change e with e' in RD end.
      zstep. zstep; if_cases K0; zify_cond K0;
        [ first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K0; clear K0; shadow_cleanup | shadow_dead ] ].
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. shadow_addr SHV 8. zstep. zstep. zstep.
      zstep; if_cases K1; zify_cond K1;
        [ first [ shadow_fast K1; clear K1; shadow_cleanup | shadow_dead ]
        | first [ shadow_fast K1; clear K1; shadow_cleanup | shadow_dead ] ].
      zstep. zstep. zstep.
      vchk SHV0 EzsV 8 0. zstep.
      zstep. shadow_chk0 SHc 8. zstep. zstep. shadow_chk0 SHw 8.
      vchk SHV0 EzsV 8 0. zstep. zstep.
      zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. carve_frame 48%nat ST. replace (pe_sp E + -304 + -48) with (pe_sp E + -352) in * by (clear; lia).
      do 8 zstep.
      lazymatch goal with FRs : rw_cells _ ?mx (pe_sp E + -352) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame FRs ST (pe_sp E + -304) end.
      replace (pe_sp E + -304) with (pe_sp E - 304) in * by (clear; lia).
      lazymatch goal with X : rw_cells rsegs ?mx (h_ff (pe_H E) + 1336) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (rw_cells_forget _ _ _ _ X) as [cnt' CNT']; cbn [cells_size csize Nat.add] in CNT'; clear X end.
      replace (h_ff (pe_H E) + 1336) with (h_ff (pe_H E) + 32 + 1304) in CNT' by lia.
      replace (pe_sp E + -352) with (pe_sp E - 304 - 48) in MU by (clear; lia).
      apply evt_done. unfold errinl_post. unfold h_vsc, pe_fp, PARSE_FRAME.
      do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [|exact ST].
      split; [exact HFR|]. split; [| split].
      + eapply (glob_ok_intro LPA); cbn [vi_bss_vsc vi_bss_cp VIA]; unfold h_vsc, h_cp; [exact BSSV| exact BSS| exact CP| exact CNT'].
      + eapply (hobj_ok_munch LPA); [exact HOBJ| exact MU| exact WM|].
        intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. lia.
      + eapply hshadow_munch; [exact HSH| exact MU| exact HG|].
        intros a Ha. unfold HFSIZE in Ha. change (8192 / 8) with 1024 in Ha. cbn [outside].
        pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFB. rewrite SHMAX_val in SHFB. lia.
  Qed.
End S.
End A_PHkg6.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcrk.A_PHkg6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.

Module A_PHarb.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_PHcrk.A_PHkg6.
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


Ltac icall_consts_in H ::= unfold errinl_post, vep_error_post, VEPERR_STACK in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HVE : vep_error_stmt.

  #[using="HVE"] Lemma PH_ESI_Include : handler_stmt S_ESI_Include.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 304 - 64, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (WZh : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
    all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
    2:{ (* [comment removed for export] *)
      unhide DJfV.
      try clear DBY. icall (errinl_spec 0x8c608 0x8c6d4 E A (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) j0 j8 (pe_lo E) zsV) by
        (first [ right; split; reflexivity | exact PE | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact HENV | exact CE
               | exact FR | exact SHV0 | exact EzsV | exact VEP16 | exact VEPhi | exact DJfV | exact STK | exact CEIL | exact MI
               | try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia | unfold pe_fp, PARSE_FRAME; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      try rename x0 into ex0; try rename x1 into ex1; try rename x2 into ex2; try rename x3 into ex3; try rename x4 into ex4; try rename x5 into ex5.
      lazymatch goal with X : henv_ok _ _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HENV1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2 end.
      unfold pe_fp, PARSE_FRAME in STK |- *.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. zstep. destruct B_et as [ET|ET]; rewrite ET, sx32_small by (clear; lia).
    all: zstep; if_cases K2; zify_cond K2; try (exfalso; try (generalize alloc_ceiling_val); clear - K2; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K2 by (clear; lia); lia); clear K2.
    2:{ (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      unhide DJfV.
      try clear DBY. icall (HVE (pe_VEP E) (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) (pe_H E) (pe_lo E)) by
        (rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - FRB; try pose proof alloc_ceiling_val; lia);
         first [ reflexivity | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact GLOB | exact HOBJ | exact HSH | exact HG
               | exact CE | exact SHVD | exact KHV | exact M8V | exact VEPhi | exact DJV | exact STK | exact CEIL | exact MI
               | unfold VEPERR_STACK; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      lazymatch goal with X : glob_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into GLOB1 end.
      lazymatch goal with X : hobj_ok _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HOBJ1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV1 : henv_ok LPA VIA (pe_H E) A v)
          by (split; [exact HFR| split; [exact GLOB1| split; [exact HOBJ1|]]];
              eapply hshadow_munch; [exact HSH| exact MU| exact HG|];
              intros a__ Ha__; unfold HFSIZE in Ha__; change (8192 / 8) with 1024 in Ha__; cbn [outside]; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo LOP CEIL ACV EVSC G2; try pose proof alloc_ceiling_val; lia);
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2
      end.
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia)
      end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x) S_TagError (fupd (x_v x) Fstate (vi_st VIA S_TagError)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
      - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
 }
    (* [comment removed for export] *)
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep. zstep.
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (fupd (x_v x) Fdostuff (vi_do_include VIA)) Fstate (vi_st VIA S_InTag)) Fattr TBL_attr_include) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) right; left. reflexivity.
      + (* [comment removed for export] *) right. split; [reflexivity|]. split; [reflexivity|]. left. exact I.
      + (* [comment removed for export] *) eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| split; [exact HFR| split; [exact GLOB| split; [exact HOBJ| exact HSH]]]].
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha].
    - assumption.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHarb.

   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Ltac icall_consts_in H ::= unfold errinl_post, VEPERR_STACK in H.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_CommentESI : handler_stmt S_CommentESI.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_sp E - 304 - 48, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_sp E - 304 - 48, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_sp E - 304 - 48, pe_sp E - 304); (pe_VEP E, pe_VEP E + 312); (h_vsc (pe_H E) + 1304, h_vsc (pe_H E) + 1320)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (WZh : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                          [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    pose proof (cenv_intro A m md AINV) as CE. fold_aview.
    pose proof HENV as (_ & GLOB & HOBJ & HSH).
    assert (SHVD : shadowed LPA (aview A m) (pe_VEP E) 312).
    { exists (pe_VEP E), 312. split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|].
      split; [try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]. try (generalize alloc_ceiling_val); clear - VEPlo VEPhi; try pose proof alloc_ceiling_val. lia. }
    assert (KHV : kHighMemBeg <= pe_VEP E) by (unfold kHighMemBeg; try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia).
    assert (M8V : pe_VEP E mod 8 = 0) by (try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia).
    assert (DJV : h_ff (pe_H E) + HFSIZE <= pe_VEP E \/ pe_VEP E + 312 <= h_ff (pe_H E)) by (unhide_djf; unfold HFSIZE; try (generalize alloc_ceiling_val); clear - DJfV; try pose proof alloc_ceiling_val; lia).
    assert (EVSC : h_vsc (pe_H E) = h_ff (pe_H E) + 32) by reflexivity. unfold kHighMemBeg in G2. all_app_facts.
    pose proof (sh_boundL (Clg:=Clg) (h_ff (pe_H E)) 8192 ltac:(try (generalize alloc_ceiling_val); clear -G2; try pose proof alloc_ceiling_val; lia) ltac:(clear; lia) G3) as SHFB. rewrite SHMAX_val in SHFB.
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. vchk SHV0 EzsV 4 0. zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
    all: zstep; zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
    - (* [comment removed for export] *)
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
      (* [comment removed for export] *)
      zstep. rewrite (shr3_div8 (pe_VEP E + 200)). vrechk SHV0 EzsV (pe_VEP E + 200) 8 0.
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. rewrite (shr3_div8 (pe_VEP E + 208)). vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
      zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MUh WMh WZh); [intros a__ Ha__; cbn [outside]; unhide_djf; unfold h_vsc, pe_fp, PARSE_FRAME in *; first [clear - Ha__ DJfV DJfS DJfB DJfD; lia | lia]| exact HENV]) end.
      astop AINV MU WM CFP. fold_cl_segs.
      set (xc := PST (x_p x) S_NxtTag (fupd (fupd (fupd (x_v x) Fesicmt LIT_arrow) Fesicmt_p LIT_arrow) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
      { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) right. split; [reflexivity|]. unfold LIT_arrow; cbn; clear; lia.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha]. }
      eapply (mark_call HMC E xc A _ _ T (x_p x) (x_p x) 1 0x8c440);
        [ exact PE | exact PIc | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
        | subst xc; cbn [x_p]; clear; lia | subst xc; cbn [x_p]; exact PLE | right; reflexivity | clear; lia | reflexivity
        | subst xc; cbn [x_st]; intros [X|X]; discriminate X | ].
      subst xc.
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; cbn [x_st after_mark]; first [reflexivity | exact ST]).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1; try pose proof alloc_ceiling_val.
    world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1 in PLT |- *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite ST1 in VEPC. cbn [stA] in VEPC.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) S_NxtTag (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (vi_st VIA S_NxtTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
    - (* [comment removed for export] *)
      unhide DJfV.
      try clear DBY. icall (errinl_spec 0x8c324 0x8c3ec E A (fupd (x_v x) Fstate (stA (x_st x))) (x_tag x) (x_q x) j0 j8 (pe_lo E) zsV) by
        (first [ left; split; [reflexivity| split; reflexivity] | exact PE | exact VEPC | exact TAG | exact PADS | exact (proj1 BASE) | exact HENV | exact CE
               | exact FR | exact SHV0 | exact EzsV | exact VEP16 | exact VEPhi | exact DJfV | exact STK | exact CEIL | exact MI
               | try (generalize alloc_ceiling_val); clear - VEPlo; try pose proof alloc_ceiling_val; lia | unfold pe_fp, PARSE_FRAME; try (generalize alloc_ceiling_val); clear - LOP; try pose proof alloc_ceiling_val; lia ]).
      hide DJfV.
      try rename x0 into ex0; try rename x1 into ex1; try rename x2 into ex2; try rename x3 into ex3; try rename x4 into ex4; try rename x5 into ex5.
      lazymatch goal with X : henv_ok _ _ _ _ ?v |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into HENV1 end.
      lazymatch goal with X : stk _ ?v _ _ |- evt _ _ (MS _ _ _ _ _ ?v _) => rename X into STK end.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] v) as MU2; pose proof (wmono_refl rsegs v) as WM2 end.
      unfold pe_fp, PARSE_FRAME in STK |- *.
      (* [comment removed for export] *)
      zstep. rewrite (shr3_div8 (pe_VEP E + 200)). vrechk SHV0 EzsV (pe_VEP E + 200) 8 0.
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. rewrite (shr3_div8 (pe_VEP E + 208)). vrechk SHV0 EzsV (pe_VEP E + 208) 8 0.
      zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?v _) =>
        assert (HENV2 : henv_ok LPA VIA (pe_H E) A v)
          by (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
              intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold HOBJ_END, HFSIZE, h_cp in Ha__; change (8192 / 8) with 1024 in Ha__;
              cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha__ SHFB VEPlo VEPhi ACV EVSC G2 DJfV; try pose proof alloc_ceiling_val; lia) end.
      clear HENV1.
      astop AINV MU WM CFP. fold_cl_segs.
      set (xc := PST (x_p x) S_NxtTag (fupd (fupd (fupd (x_v x) Fesicmt LIT_arrow) Fesicmt_p LIT_arrow) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
      { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) right. split; [reflexivity|]. unfold LIT_arrow; cbn; clear; lia.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR; [left; left; unfold blk; lia | left; right; right; right; exact Ha]. }
      eapply (mark_call HMC E xc A _ _ T (x_p x) (x_p x) 1 0x8c440);
        [ exact PE | exact PIc | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
        | subst xc; cbn [x_p]; clear; lia | subst xc; cbn [x_p]; exact PLE | right; reflexivity | clear; lia | reflexivity
        | subst xc; cbn [x_st]; intros [X|X]; discriminate X | ].
      subst xc.
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
    assert (ST1 : x_st x1 = S_NxtTag) by (rewrite EX1; cbn [x_st after_mark]; first [reflexivity | exact ST]).
    assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
    assert (EP1 : x_p x1 = x_p x) by (rewrite EX1; reflexivity).
    clear - HMC PE ST PLT KL KX PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1; try pose proof alloc_ceiling_val.
    world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1 in PLT |- *.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
    assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      rewrite ST1 in VEPC. cbn [stA] in VEPC.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) S_NxtTag (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fstate (vi_st VIA S_NxtTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      + assumption.
      + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
