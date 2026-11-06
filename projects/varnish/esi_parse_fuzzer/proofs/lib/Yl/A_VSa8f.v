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
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_AI16.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module A_VS6ke.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_AI16.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vsb_zero_cells : list cell :=
  [ C4 (w64 0); C4 (w64 0); C8 (w64 0); C8 (w64 0); C8 (w64 0); C4 (w64 0); C4 (w64 0) ].
Lemma vsb_zero_cells_bytes : cells_bytes vsb_zero_cells = repeat (Z_to_bv 8 0) 40.
Proof. vm_compute. reflexivity. Qed.

Ltac icall_consts_in H ::= unfold asan_memset_post, ASAN_MEMSET_STACK in H.

Lemma pa_site_10f838 : In 0x89a94 (cl_sites LPA). Proof. cbn. tauto. Qed.
Lemma pa_site_10f8ac : In 0x89b1c (cl_sites LPA). Proof. cbn. tauto. Qed.
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  #[using="AI16"] Lemma VSB_new_auto_ok : VSB_new_auto_stmt.
  Proof.
    unfold VSB_new_auto_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI LIVEX NLVX PCM S0C TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    pose proof alloc_ceiling_num as ACV.
    unfold NEWAUTO_STACK, ASTK in *. unfold VSB_new_auto_entry.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (map_cells_of_consts _ (consts_hold_ainv LPA A m md AINV)) as MC. fold_aview. open_map_cells MC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8256, bv_unsigned sp)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] | exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 8 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 64) 64 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF end.
    eapply (as_malloc_cps16 (AsanAlloc16:=AI16)) with (n := 40);   (* [comment removed for export] *)
      [ exact AINV0 | exact MI | reflexivity | unfold REQ_MAX; lia | rewrite NREQ_CAP_eq; lia | lia
      | try (generalize alloc_ceiling_val); clear - NLVX; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; unfold kMaxPrimaryUser in X; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite prim_cost_40; clear - PCM; lia (* [comment removed for export] *) | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; apply pa_site_10f838
      | exact S0C
      | rewrite unsigned_lit by lia; unfold ASTK; lia
      | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r1 A1 mA1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 HLE1 FRS1 TCR1 OUT1 FRK1. cbn [Z.ltb] in TCR1. rewrite Z.sub_0_r in TCR1.
    fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK1 by lia. unfold ASTK in FRK1.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
    destruct OUT1 as (NZ1 & FRESH1 & LIVEr1 & LIVEq1 & LBY1 & NL1 & SC1 & PC1); cbn [Z.ltb kMaxPrimaryUser] in SC1; rewrite ?Z.sub_0_r in SC1. rewrite prim_cost_40 in PC1.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      acall_xfer FRK1.
      (first [ pose proof ((live_geomP LPA A1 mA1 md1 r1 _ AINV1 LIVEr1)) as dR_1; dand7 dR_1 as _ R16 Rlo Rhi Rimg Rmap Rown | pose proof (live_geomP LPA A1 mA1 md1 r1 _ AINV1 LIVEr1) as (_ & R16 & Rlo & Rhi & Rimg & Rmap & Rown) ]).
      unfold kHighMemBeg in Rlo. all_app_facts.
      (first [ pose proof ((newblock_cells (L:=LPA) A1 mA1 md1 r1 _ AINV1 LIVEr1)) as dR_2; dex1 dR_2 as junk1; dand3 dR_2 as LJ1 NB1 CR1 | pose proof ((newblock_cells (L:=LPA) A1 mA1 md1 r1 _ AINV1 LIVEr1)) as dR_2; dand4 dR_2 as junk1 LJ1 NB1 CR1 | destruct (newblock_cells (L:=LPA) A1 mA1 md1 r1 _ AINV1 LIVEr1) as (junk1 & LJ1 & NB1 & CR1) ]).
      pose proof (as_live_shadow LPA A1 mA1 md1 r1 40 AINV1 LIVEr1) as SHB1. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) r1 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHB1B. rewrite SHMAX_val in SHB1B.
      pose proof (sh_boundL (Clg:=Clg) r1 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHB1N. rewrite SHMAX_val in SHB1N.
      pose proof (asan_memset_cells_of_consts _ (consts_hold_ainv LPA A1 mA1 md1 AINV1)) as AMC. fold_aview.
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp); (r1, r1 + 40)] (aview A1 mA1)) as MU2.
      pose proof (wmono_refl rsegs (aview A1 mA1)) as WM2.
      pose proof (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA)) as MAPF.
      cbn [cells_size csize Nat.add length] in MAPF. replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) in MAPF by lia.
      assert (WMAP : mapped (aview A1 mA1) (bv_unsigned sp - 8256) 8256).
      { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
      assert (CFP2 : client_fp LPA A1 (aview A1 mA1) [(bv_unsigned sp - 8256, bv_unsigned sp); (r1, r1 + 40)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8256)) with 8256 by lia; exact WMAP |].
        split; [right; left; exists r1, 40; split; [exact LIVEr1|lia]| exact I]. }
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
      zstep. zstep. zstep. zstep.
      icall asan_memset_spec by
        (rewrite ?unsigned_lit by lia;
         first [ exact NB1 | exact MI1 | exact AMC | exact ST | exact CEIL
               | unfold ASAN_MEMSET_STACK; lia
               | (left; lia)
               | lia
               | (right; eapply live_range_ok; [exact AINV1 | exact LIVEr1 | lia | lia | lia]) ]).
      (* [comment removed for export] *)
      lazymatch goal with X : rw_cells _ ?mx r1 [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into NBZ end.
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      change (Z.to_nat 40) with 40%nat in NBZ. change (0 mod 256) with 0 in NBZ.
      apply (rw_cells_recast rsegs _ r1 _ vsb_zero_cells) in NBZ; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | exact vsb_zero_cells_bytes].
      unfold vsb_zero_cells in NBZ.
      (* [comment removed for export] *)
      shadow_chk SHB1 4 11.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      rewrite (shr3_div8 (r1 + 32)). shadow_rechk SHB1 (r1 + 32) 4 11.
      (* [comment removed for export] *)
      zstep. zstep. zstep. shadow_chk0 SHB1 8.
      (* [comment removed for export] *)
      zstep. zstep. shadow_chk0 SHB1 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
      (* [comment removed for export] *)
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mB end.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ (aview A1 mx) (bv_unsigned sp - 64) 64 AINV2 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF2;
        pose proof (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ r1 40 r1 40 AINV2 LIVEr1 ltac:(lia) ltac:(lia) ltac:(lia)) as CR1'
      end.
      (* [comment removed for export] *)
      lazymatch type of MU2 with munch _ _ ?mx =>
        assert (CFa : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8256 nowhere (newblk r1 40) (aview A m) mx)
      end.
      { eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 mA1) _ _ _);
          [ exact MU | | exact FRK1 | lia | lia | intros a X; destruct X | intros a X; left; exact X
          | exact MU2 | | ].
        - intros a Ha NO. cbn [outside] in NO. lia.
        - intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
        - lazymatch goal with |- mapped ?v _ _ =>
            eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] end. }
      eapply (as_malloc_cps16 (AsanAlloc16:=AI16)) with (n := 16);
        [ exact AINV2 | assumption | reflexivity | unfold REQ_MAX; lia | rewrite NREQ_CAP_eq; lia | rewrite LBY1; lia
        | try (generalize alloc_ceiling_val); clear - NL1 NLVX; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia | intros X; exfalso; unfold kMaxPrimaryUser in X; try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val as ACV__; lia
        | rewrite prim_cost_16; clear - PCM PC1; lia (* [comment removed for export] *) | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; reflexivity
        | rewrite unsigned_lit by lia; apply pa_site_10f8ac
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; unfold ASTK; lia
        | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
        | ].
      clear MU WM CFP FRK1.
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' r2 A2 mA2 md4. cbv zeta.
      intros AINV3 MI3 MDF3 HLE3 FRS3 TCR3 OUT3 FRK3. cbn [Z.ltb] in TCR3. rewrite Z.sub_0_r in TCR3.
      fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK3 by lia. unfold ASTK in FRK3.
      pose proof (as_minv LPA A1 _ _ AINV2) as [_ MH2].
      destruct OUT3 as (NZ2 & FRESH2 & LIVEr2 & LIVEq3 & LBY3 & NL3 & SC3 & PC3); cbn [Z.ltb kMaxPrimaryUser] in SC3; rewrite ?Z.sub_0_r in SC3. rewrite prim_cost_16 in PC3.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      + (* [comment removed for export] *)
        acall_xfer FRK3.
        assert (NE12 : r1 <> r2) by (intros ->; rewrite FRESH2 in LIVEr1; discriminate).
        assert (LIVEr1' : a_live A2 r1 = Some 40) by (rewrite (LIVEq3 r1 NE12); exact LIVEr1).
        (first [ pose proof ((live_geomP LPA A2 mA2 md4 r2 _ AINV3 LIVEr2)) as dR_3; dand7 dR_3 as _ B16 Blo Bhi Bimg Bmap Bown | pose proof (live_geomP LPA A2 mA2 md4 r2 _ AINV3 LIVEr2) as (_ & B16 & Blo & Bhi & Bimg & Bmap & Bown) ]).
        unfold kHighMemBeg in Blo. all_app_facts.
        pose proof (as_live_disjoint LPA A2 mA2 md4 r1 40 r2 16 AINV3 LIVEr1' LIVEr2 NE12) as DRB.
        (first [ pose proof ((newblock_cells (L:=LPA) A2 mA2 md4 r2 _ AINV3 LIVEr2)) as dR_4; dex1 dR_4 as junkb; dand3 dR_4 as LJb NB2 CR2 | pose proof ((newblock_cells (L:=LPA) A2 mA2 md4 r2 _ AINV3 LIVEr2)) as dR_4; dand4 dR_4 as junkb LJb NB2 CR2 | destruct (newblock_cells (L:=LPA) A2 mA2 md4 r2 _ AINV3 LIVEr2) as (junkb & LJb & NB2 & CR2) ]).
        pose proof (as_live_shadow LPA A2 mA2 md4 r1 40 AINV3 LIVEr1') as SHB3. fold_cl_segs. fold_aview.
        pose proof (munch_refl [(bv_unsigned sp - 8256, bv_unsigned sp); (r1, r1 + 40)] (aview A2 mA2)) as MU3.
        pose proof (wmono_refl rsegs (aview A2 mA2)) as WM3.
        assert (WMAP3 : mapped (aview A2 mA2) (bv_unsigned sp - 8256) 8256).
        { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
        assert (CFP3 : client_fp LPA A2 (aview A2 mA2) [(bv_unsigned sp - 8256, bv_unsigned sp); (r1, r1 + 40)]).
        { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8256)) with 8256 by lia; exact WMAP3 |].
          split; [right; left; exists r1, 40; split; [exact LIVEr1'|lia]| exact I]. }
        ago AINV3. fold_cl_segs.
        (* [comment removed for export] *)
        shadow_rechk0 SHB3 (r1 + 8) 8.
        zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
        (* [comment removed for export] *)
        shadow_rechk SHB3 (r1 + 32) 4 11.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        try (match type of NBZ with context [Z.lor ?x ?y] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v in NBZ end).
        zstep.
        (* [comment removed for export] *)
        zstep. do 7 zstep. zstep. zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        astop AINV3 MU3 WM3 CFP3.
        pose proof (as_minv LPA A2 _ _ AINV4) as [_ MH4].
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r1 A2 mx mdx) end;
          [ assumption | assumption | | | | | | exact ST | ].   (* [comment removed for export] *)
        { eapply amd_frame_sbm_l; [exact SBM | exact MH |].
          eapply amd_frame_trans; [exact MDF1|]. eapply amd_frame_sbm_l; [exact SBM0 | exact (proj2 (as_minv LPA A1 _ _ AINV1)) |].
          eapply amd_frame_sbm_r; [exact MDF3 | eassumption]. }
        { intros ff. rewrite FRS3. apply FRS1. }
        { rewrite TCR3, TCR1. reflexivity. }
        { rewrite SC3, SC1. reflexivity. }
        { rewrite PC3, PC1. clear; lia. }   (* [comment removed for export] *)
        exists r2. split; [exact NZ1|]. split; [|split; [exact FRESH1|]; split; [|split; [|split; [|split]]]].
        * (* [comment removed for export] *)
          unfold vsb_fresh. split. { unfold vsb_cells. cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf]. exact NBZ. }
          split. { unfold vsb_inv, VSB_FLAGS_LIVE; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf].
                   OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [lia | reflexivity | left; reflexivity]. }
          cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf].
          split; [exact LIVEr1'|]. split; [exact LIVEr2|]. split; [exact NE12|].
          exists junkb. split; [eapply u8arr_of_rw_cells; exact NB2|]. split; [cbn [vb_size]; lia| intros X; discriminate X].
        * rewrite <- (LIVEq1 r2 ltac:(intros E; exact (NE12 (eq_sym E)))). exact FRESH2.
        * intros q Q1 Q2. rewrite (LIVEq3 q Q2). apply LIVEq1, Q1.
        * rewrite LBY3, LBY1. lia.
        * rewrite NL3, NL1. lia.
        * lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
            assert (CFb : cframe LPA (owned A1) (owned A2) (bv_unsigned sp) 8256 (newblk r1 40) (newblk r2 16) (aview A1 mB) vfin)
              by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A1 mB) (aview A1 mB) (aview A2 mA2) _ [] _);
                  [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK3 | lia | lia
                  | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                  | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ];
                  intros a Ha NO; cbn [outside] in NO; unfold newblk, blk; lia);
            eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 mB) vfin CFa CFb); [lia | lia
                | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]
                | intros a X; destruct X | intros a X; left; exact X
                | intros a [X|X]; [left; exact X| right; left; exact X] ]
          end.
  Qed.
End S.
End A_VS6ke.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold newblk, frm in X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Section Loop.
    Variables (xra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
              (F : bvmap 5 word) (fc : bv 32) (m : mem) (sz : Z).
    Hypothesis SZ : 0 <= sz <= 4095.

    Notation AT pc xa3 xs2 :=
      (MS (mkR xra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 sz) a2 xa3 a4 a5 a6 a7
              xs2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

    #[using="SZ"] Lemma ext_loop : forall (k : nat) (ns : Z) (xs2 : word),
      0 < ns -> sz <= ns * 2 ^ Z.of_nat k -> ns <= 8192 ->
      evt rsegs (fun ms => ms = AT 0x8a200 (Z_to_bv 64 (2 * vsb_dbl k ns sz)) (Z_to_bv 64 (vsb_dbl k ns sz)))
                (AT 0x8a1e0 (Z_to_bv 64 ns) xs2).
    Proof.
      induction k as [|k IH]; intros ns xs2 Hns Hsz Hle.
      - rewrite Z.pow_0_r in Hsz. cbn [vsb_dbl].
        zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. unsign K. klia K. }
        zstep. apply evt_done. shl1_to_mul. reflexivity.
      - rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hsz by lia.
        cbn [vsb_dbl]. destruct (Z.ltb_spec ns sz) as [Hlt|Hge].
        + zstep. zstep. zstep. if_cases K; zify_cond K.
          2:{ exfalso. unsign K. klia K. }
          shl1_to_mul. apply IH; [lia | nia | lia].
        + zstep. zstep. zstep. if_cases K; zify_cond K. { exfalso. unsign K. klia K. }
          zstep. apply evt_done. shl1_to_mul. reflexivity.
    Qed.
  End Loop.

  #[using="AI16"] Lemma VSB_extend_ok : VSB_extend_stmt.
  Proof.
    unfold VSB_extend_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI A0 A1 VOBJ AL1 AL2 LBY NLV SCM PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite A0, A1. pose proof (map_cells_of_consts _ (consts_hold_ainv LPA A m md AINV)) as MC. fold_aview.
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB0 Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB0 & Smap & Bmap) ]).
    pose proof (vsb_shadows LPA A m md S vr false AINV VOBJ) as [SHS SHB].
    pose proof VOBJ as VOBJ0. vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]).
    pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vb16 | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vb16) ]).
    pose proof alloc_ceiling_num as ACV. unfold kHighMemBeg in Slo, Blo. all_app_facts.
    fold_cl_segs. unfold vsb_cells in VSBC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    (first [ pose proof ((vsb_extendsize_spec (vb_size vr + addlen) ltac:(unfold EXT_MAX in AL2; lia))) as dR_4; dand3 dR_4 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size vr + addlen) ltac:(unfold EXT_MAX in AL2; lia)) as (NS1 & NS2 & NS3) ]).
    unfold EXT_STACK, ASTK, EXT_MAX in *. unfold VSB_extend_entry.
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB. rewrite SHMAX_val in SHSB, SHBB.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    open_map_cells MC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8272, bv_unsigned sp); (S, S + 40)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8272, bv_unsigned sp); (S, S + 40)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] |].
      split; [right; left; exists S, 40; split; [exact VLS|lia]| exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 80%nat ST.
    do 11 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk SHS 4 13.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases KC; zify_cond KC.
    { exfalso. revert KC. rewrite Vfl. vm_compute. discriminate. }
    clear KC.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    eapply (evt_cut rsegs (fun ms => exists xa3 xa4, ms =
      MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (S + 16))
              (Z_to_bv 64 S) (Z_to_bv 64 (vb_size vr + addlen)) (zx32 (Z_to_bv 64 (vb_flags vr))) xa3 xa4 a5 a6 a7
              (Z_to_bv 64 (vsb_extendsize (vb_size vr + addlen))) s3 (Z_to_bv 64 (-1)) s5
              (Z_to_bv 64 2147450880) (Z_to_bv 64 ((S + 16) / 8 + 2147450880)) (Z_to_bv 64 ((S + 32) / 8 + 2147450880))
              s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x8a200) fc None _ (seg_rom rsegs))).
    { zstep. if_cases KR; zify_cond KR; unsign KR.
      - (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. apply evt_done. eexists _, _.
        rewrite roundup_pagemask by lia. unfold vsb_extendsize.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
      - (* [comment removed for export] *)
        zstep.
        eapply evt_cut; [eapply (ext_loop) with (sz := vb_size vr + addlen) (k := 9%nat) (ns := 16); cbn; lia|].
        intros ms1 ->. apply evt_done. eexists _, _. unfold vsb_extendsize.
        rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    (intros ms1; (first [ intro dR_7; dand3 dR_7 as xa3 xa4 -> | intros (xa3 & xa4 & ->) ])).
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA. { exfalso. unsign KA. klia KA. } clear KA.
    zstep. zstep. zstep. if_cases KD; zify_cond KD.
    2:{ exfalso. revert KD. rewrite Vfl. vm_compute. discriminate. }
    clear KD.
    (* [comment removed for export] *)
    shadow_chk0 SHS 8.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    astop AINV MU WM CFP.
    fold_cl_segs.
    (* [comment removed for export] *)
    pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ S 40 S 40 AINV0 VLS ltac:(lia) ltac:(lia) ltac:(lia)) as CS.
    pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ _ _ (vb_buf vr) (Z.of_nat (length bs0)) AINV0 VLB ltac:(lia) ltac:(lia) ltac:(lia)) as CB.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 80) 80 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF end.
    eapply (as_realloc_cps16 (AsanAlloc16:=AI16)) with (old := vb_size vr);   (* [comment removed for export] *)
      [ exact AINV0 | exact MI | reflexivity | reflexivity | unfold REQ_MAX; lia
      | rewrite NREQ_CAP_eq; pose proof (vsb_extendsize_tight (vb_size vr + addlen)); lia
      | lia | exact VLB | exact LBY | exact NLV
      | intros LT16; exfalso; try (generalize alloc_ceiling_val); clear - LT16 Vsz NS1 AL1; try pose proof alloc_ceiling_val as ACV__; lia | exact SCM | exact PCM | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; apply pa_sites_ex
      | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; unfold ASTK; lia
      | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md'. cbv zeta. intros AINV' MI' MDF FRMS TCR NLV' OUT.
    assert (TCR' : a_tinycred A' = a_tinycred A).
    { rewrite TCR. replace (vsb_extendsize (vb_size vr + addlen) <? 16) with false; [lia|].
      symmetry. apply Z.ltb_ge. try (generalize alloc_ceiling_val); clear - Vsz NS1 AL1; try pose proof alloc_ceiling_val as ACV__. lia. }
    fold_cl_segs. fold_aview. rewrite unsigned_lit in OUT by lia. unfold ASTK in OUT.
    pose proof (as_minv LPA A _ _ AINV0) as [_ MH0]. pose proof (as_minv LPA A' _ _ AINV') as [_ MH'].
    destruct OUT as (NZ & NP & FRESH & LIVEr & DEADp & LIVEq & LBY' & COPY & FRK & SCR & PCR).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    { (* [comment removed for export] *)
      pose proof (as_live_disjoint LPA A _ _ S 40 (vb_buf vr) (vb_size vr) AINV0 VLS VLB VNE) as DSB.
      acall_xfer FRK.
      assert (SNR : S <> r). { intros ->. rewrite VLS in FRESH. discriminate. }
      assert (LS' : a_live A' S = Some 40). { rewrite (LIVEq S SNR VNE). exact VLS. }
      (first [ pose proof ((live_geomP LPA A' m' md' r _ AINV' LIVEr)) as dR_5; dand7 dR_5 as _ R16 Rlo Rhi Rimg Rmap Rown | pose proof (live_geomP LPA A' m' md' r _ AINV' LIVEr) as (_ & R16 & Rlo & Rhi & Rimg & Rmap & Rown) ]).
      (first [ pose proof ((newblock_cells (L:=LPA) A' m' md' r _ AINV' LIVEr)) as dR_6; dex1 dR_6 as bs1; dand3 dR_6 as LBS1 NB1 CR1 | pose proof ((newblock_cells (L:=LPA) A' m' md' r _ AINV' LIVEr)) as dR_6; dand4 dR_6 as bs1 LBS1 NB1 CR1 | destruct (newblock_cells (L:=LPA) A' m' md' r _ AINV' LIVEr) as (bs1 & LBS1 & NB1 & CR1) ]).
      fold_cl_segs. unfold kHighMemBeg in Rlo. all_app_facts.
      pose proof (as_live_disjoint LPA A' m' md' S 40 r _ AINV' LS' LIVEr SNR) as DSR.
      (* [comment removed for export] *)
      pose proof (as_live_shadow LPA A' m' md' S 40 AINV' LS') as SHS'. fold_cl_segs. fold_aview.
      (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (S, S + 40)] (aview A' m')) as MU2.
      pose proof (wmono_refl rsegs (aview A' m')) as WM2.
      pose proof (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA)) as MAPF.
      cbn [cells_size csize Nat.add length] in MAPF. replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) in MAPF by lia.
      assert (CFP2 : client_fp LPA A' (aview A' m') [(bv_unsigned sp - 80, bv_unsigned sp); (S, S + 40)]).
      { cbn. split; [left; split; [lia|]; split; [lia|];
                    replace (bv_unsigned sp - (bv_unsigned sp - 80)) with 80 by lia; exact MAPF |].
        split; [right; left; exists S, 40; split; [exact LS'|lia]| exact I]. }
      ago AINV'. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KZ; zify_cond KZ. { exfalso. klia KZ. } clear KZ.
      (* [comment removed for export] *)
      shadow_rechk SHS' (S + 32) 4 11.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        pose proof (rw_cells_read_sub rsegs mx _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF end.
      rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
      match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
      zstep. zstep. zstep. if_cases KD; zify_cond KD. 2:{ dead KD. } clear KD RDF.
      (* [comment removed for export] *)
      shadow_chk0 SHS' 8.
      zstep.
      (* [comment removed for export] *)
      shadow_rechk0 SHS' (S + 16) 8.
      zstep. zstep.
      (* [comment removed for export] *)
      zstep. do 10 zstep. zstep. zstep.
      release_frame FR ST (bv_unsigned sp).
      astop AINV' MU2 WM2 CFP2.
      set (vr' := vsb_set_buf_size vr r (vsb_extendsize (vb_size vr + addlen))).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 A' mx mdx vr') end;
        [ assumption | exact MI'
        | eapply amd_frame_sbm_l; [exact SBM | exact (proj2 (as_minv LPA A m md AINV)) | eapply amd_frame_sbm_r; [exact MDF | eassumption]]
        | split; [exact VSBC|]; split; [unfold vsb_inv; cbn [vr' vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|];
          split; [exact LS'|]; split; [exact LIVEr|]; split; [exact SNR|];
          exists bs1; split; [apply (u8arr_of_rw_cells rsegs _ _ _ _ NB1)|]; split; [cbn [vr' vsb_set_buf_size vb_size]; lia| intros X; discriminate X]
        | intros q Q1 Q2; apply LIVEq; [exact Q2|exact Q1] | exact FRMS | exact TCR' | exact NLV' | exact ST | ].
      exists r. split; [reflexivity|]. split; [reflexivity|]. split; [|split; [exact FRESH|split; [exact DEADp|split; [exact LBY'|split; [exact SCR|split; [exact PCR|]]]]]].
      + (* [comment removed for export] *)
        intros i Hi.
        lazymatch type of MU2 with munch _ _ ?vfin =>
          rewrite (MU2 (Z_to_bv 64 (r + i))) by (rewrite unsigned_lit by lia; cbn [outside]; lia) end.
        rewrite (COPY i) by lia.
        apply (MU (Z_to_bv 64 (vb_buf vr + i))). rewrite unsigned_lit by lia. cbn [outside]. lia.
      + lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
        eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A' m') vfin _ _);
          [ exact MU | | exact FRK | lia | lia | intros a X; left; exact X | intros a X; left; exact X
          | exact MU2 |
          | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ] end.
        * intros a Ha NO. cbn [outside] in NO. lia.
        * intros a Ha NO. cbn [outside] in NO. lia. }
  Qed.
End S.
