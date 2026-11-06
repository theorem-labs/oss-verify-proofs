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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Po6qc A_Img A_Cocsh A_VSe3i.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, asan_memset_post, ASAN_MEMSET_STACK in H.
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LO; @Slo; @SPR; @CEIL; @P0lo; @ACV; @Shi; @LO0; @PSCE; @P0le; @VNE; @H; @Blo; @Vsz; @Vb0; @DSB; @PSS; @PSB; @X; @SZ; @SR; @P0ge; @V16K; @V16C0; @SHBN; @NO; @SHSN; @S8; @K0; @PS8; @KU])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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

Lemma pa_site_110edc : In 0x8afa0 (cl_sites LPA). Proof. cbn. tauto. Qed.
Lemma pa_site_110efc : In 0x8afc0 (cl_sites LPA). Proof. cbn. tauto. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma VSB_destroy_ok : VSB_destroy_stmt.
  Proof.
    unfold VSB_destroy_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI A0 PSC CO PS8 PSCE VOBJ TP SP16 ST CEIL LO K.
    rewrite A0. pose proof alloc_ceiling_num as ACV.
    unfold DESTROY_STACK, ASTK in *. unfold VSB_destroy_entry.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr fin AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr fin AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (vsb_shadows LPA A m md S vr fin AINV VOBJ) as [SHS _]. fold_cl_segs.
    vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts. unfold vsb_cells in VSBC.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSN. rewrite SHMAX_val in SHSN.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBN. rewrite SHMAX_val in SHBN.
    (* [comment removed for export] *)
    (first [ pose proof ((cobj_open (Clg:=Clg) LPA A m md _ PS 8 AINV CO ltac:(lia))) as dR_4; dex2 dR_4 as p0 sz0; dand9 dR_4 as SHP P08 P0lo P0le P0ge P0ce HOME CRP PDJ | pose proof ((cobj_open (Clg:=Clg) LPA A m md _ PS 8 AINV CO ltac:(lia))) as dR_4; dand11 dR_4 as p0 sz0 SHP P08 P0lo P0le P0ge P0ce HOME CRP PDJ | destruct (cobj_open (Clg:=Clg) LPA A m md _ PS 8 AINV CO ltac:(lia)) as (p0 & sz0 & SHP & P08 & P0lo & P0le & P0ge & P0ce & HOME & CRP & PDJ) ]).
    fold_cl_segs. unfold kHighMemBeg in P0lo. all_app_facts. clear CRP.
    pose proof (shpat_sh_boundL (Clg:=Clg) p0 sz0 ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB. rewrite SHMAX_val in SHPB.
    assert (PSS : PS + 8 <= S - 16 \/ S + 40 <= PS \/ (PS + 8 <= S /\ 40 = 40)) by (apply (PDJ S 40 VLS); cbn; tauto).
    assert (PSB : PS + 8 <= vb_buf vr - 16 \/ vb_buf vr + vb_size vr <= PS \/ (PS + 8 <= vb_buf vr /\ vb_size vr = vb_size vr))
      by (apply (PDJ (vb_buf vr) (vb_size vr) VLB); cbn; tauto).
    clear PDJ.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. open_map_cells MC.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8224, bv_unsigned sp)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] | exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 32%nat ST.
    do 5 zstep.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { exfalso. klia K0. } clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; lia. } clear KU.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk0 SHP 8.
    (* [comment removed for export] *)
    zstep. zstep.
    icall (assert_VSB_integrity_ok)
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact ST
                | assumption
                | lia ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    (* [comment removed for export] *)
    shadow_rechk0 SHP PS 8.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; lia. } clear KU.
    zstep.
    (* [comment removed for export] *)
    shadow_chk SHS 4 13.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases KD; zify_cond KD. { exfalso. revert KD. rewrite Vfl. destruct fin; vm_compute; congruence. } clear KD.
    zstep. zstep. if_cases KT; zify_cond KT. { exfalso. revert KT. rewrite Vfl. destruct fin; vm_compute; congruence. } clear KT.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8. zstep. zstep.
    (* [comment removed for export] *)
    clear SHS. astop AINV MU WM CFP. fold_cl_segs.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 32) 32 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF;
      pose proof (crange_block (Clg:=Clg) (L:=LPA) A _ _ S 40 S 40 AINV0 VLS ltac:(lia) ltac:(lia) ltac:(lia)) as CS;
      pose proof (chome_crange (Clg:=Clg) LPA A _ _ _ p0 sz0 PS 8 AINV0 HOME P0le P0ge ltac:(lia)) as CRP0 end.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
    eapply (as_free_cps LPA) with (p := vb_buf vr) (n0 := vb_size vr);
      [ exact AINV0 | assumption | reflexivity | right; exact VLB | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; apply pa_site_110edc
      | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; unfold ASTK; lia
      | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 _ FRS1 DEADb LIVEq1 LBY1 TCR1 SCR1 PCR1 NL1 ERRNO1 FRK1.   (* [comment removed for export] *)
    replace (vb_buf vr =? 0) with false in NL1 by (symmetry; apply Z.eqb_neq; try (generalize alloc_ceiling_val); clear - Blo; try pose proof alloc_ceiling_val as ACV__; lia).
    fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK1 by lia. unfold ASTK in FRK1.
    (* [comment removed for export] *)
    destruct (chome_call (Clg:=Clg) LPA A A1 _ _ m1 md1 _ _ _ _ _ _ [S] p0 sz0 AINV0 HOME SHP ltac:(lia) (cframe_of_frame_ok LPA _ _ _ _ _ _ _ _ FRK1)
                ltac:(lia)) as [SHP1 HOME1];
      [ intros p k LP NI; split; [rewrite LIVEq1; [exact LP| intros ->; apply NI; cbn; tauto] | cbn; cbn in NI; tauto]
      | intros ff kk age HF; rewrite FRS1; exact HF
      | intros xv ff kk age X HF; eapply (newblk_avoids_fshadow LPA A _ _ (vb_buf vr) (vb_size vr)); [exact AINV0| exact VLB| exact HF| exact X]
      | exact AINV1 | reflexivity | ].
    clear SHP HOME.
    acall_xfer FRK1.
    assert (LS1 : a_live A1 S = Some 40) by (rewrite (LIVEq1 S VNE); exact VLS).
    pose proof (as_live_shadow LPA A1 m1 md1 S 40 AINV1 LS1) as SHS1. fold_cl_segs. fold_aview.
    pose proof (asan_memset_cells_of_consts _ (consts_hold_ainv LPA A1 m1 md1 AINV1)) as AMC. fold_aview.
    (* [comment removed for export] *)
    destruct (rw_cells_forget _ _ _ _ VSBC) as [junkS VSBS]. cbn [cells_size csize Nat.add] in VSBS.
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (S, S + 40); (PS, PS + 8)] (aview A1 m1)) as MU2.
    pose proof (wmono_refl rsegs (aview A1 m1)) as WM2.
    assert (WMAP2 : mapped (aview A1 m1) (bv_unsigned sp - 8224) 8224).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP2 : client_fp LPA A1 (aview A1 m1) [(bv_unsigned sp - 8224, bv_unsigned sp); (S, S + 40); (PS, PS + 8)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8224)) with 8224 by lia; exact WMAP2 |].
      split; [right; left; exists S, 40; split; [exact LS1|lia]|].
      split; [| exact I]. right. destruct (chome_fp LPA A1 [S] p0 sz0 PS 8 HOME1 P0le P0ge) as [X|X]; [left; exact X| right; left; exact X]. }
    ago AINV1. fold_cl_segs.
    (* [comment removed for export] *)
    shadow_rechk0 SHP1 PS 8.
    zstep. zstep. zstep. zstep.
    icall asan_memset_spec by
      (rewrite ?unsigned_lit by lia;
       first [ exact VSBS | exact MI1 | exact AMC | exact ST | exact CEIL
             | unfold ASAN_MEMSET_STACK; lia
             | (left; lia)
             | lia
             | (right; eapply live_range_ok; [exact AINV1 | exact LS1 | lia | lia | lia]) ]).
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
    lazymatch goal with X : rw_cells _ ?mx S [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into NBZ end.
    (* [comment removed for export] *)
    zstep. zstep.
    (* [comment removed for export] *)
    astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ (aview A1 mx) (bv_unsigned sp - 32) 32 AINV2 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF2;
      pose proof (chome_crange (Clg:=Clg) LPA A1 _ _ _ p0 sz0 PS 8 AINV2 HOME1 P0le P0ge ltac:(lia)) as CRP2;
      (* [comment removed for export] *)
      assert (CFa : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8224
                       (fun a => newblk S 40 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (PS <= a < PS + 8)) nowhere (aview A m) (aview A1 mx))
        by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 m1) _ _ _);
            [ exact MU | | exact FRK1 | lia | lia | intros a X; right; left; exact X | intros a X; destruct X
            | exact MU2 | | eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
            [ intros a Ha NO; cbn [outside] in NO; lia
            | intros a Ha NO; cbn [outside] in NO; unfold newblk, blk; lia ])
    end.
    pose proof (as_minv LPA A1 _ _ AINV2) as [_ MH2].
    eapply (as_free_cps LPA) with (p := S) (n0 := 40);
      [ exact AINV2 | assumption | reflexivity | right; exact LS1 | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; apply pa_site_110efc
      | rewrite unsigned_lit by lia; lia
      | rewrite unsigned_lit by lia; unfold ASTK; lia
      | rewrite unsigned_lit by lia; unfold ASTK; eapply (stk_mapped (L:=LPA)); [exact ST| exact CEIL | lia | lia]
      | ].
    intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A2 m3 md3. cbv zeta.
    intros AINV3 MI3 MDF3 _ FRS3 DEADS LIVEq3 LBY3 TCR3 SCR3 PCR3 NL3 ERRNO3 FRK3.   (* [comment removed for export] *)
    replace (S =? 0) with false in NL3 by (symmetry; apply Z.eqb_neq; try (generalize alloc_ceiling_val); clear - Slo; try pose proof alloc_ceiling_val as ACV__; lia).
    fold_cl_segs. fold_aview. rewrite unsigned_lit in FRK3 by lia. unfold ASTK in FRK3.
    destruct (chome_call (Clg:=Clg) LPA A1 A2 _ _ m3 md3 _ _ _ _ _ _ [] p0 sz0 AINV2 HOME1 SHP1 ltac:(lia) (cframe_of_frame_ok LPA _ _ _ _ _ _ _ _ FRK3)
                ltac:(lia)) as [SHP3 HOME3];
      [ intros p k LP NI; split; [rewrite LIVEq3; [exact LP| intros ->; apply NI; cbn; tauto] | cbn; tauto]
      | intros ff kk age HF; rewrite FRS3; exact HF
      | intros xv ff kk age X HF; eapply (newblk_avoids_fshadow LPA A1 _ _ S 40); [exact AINV2| exact LS1| exact HF| exact X]
      | exact AINV3 | reflexivity | ].
    clear SHP1 HOME1 SHS1 NBZ.
    acall_xfer FRK3. clear MU2 WM2 CFP2.
    pose proof (munch_refl [(bv_unsigned sp - 8224, bv_unsigned sp); (PS, PS + 8)] (aview A2 m3)) as MU3.
    pose proof (wmono_refl rsegs (aview A2 m3)) as WM3.
    assert (WMAP3 : mapped (aview A2 m3) (bv_unsigned sp - 8224) 8224).
    { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP3 : client_fp LPA A2 (aview A2 m3) [(bv_unsigned sp - 8224, bv_unsigned sp); (PS, PS + 8)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8224)) with 8224 by lia; exact WMAP3 |].
      split; [| exact I]. right. destruct (chome_fp LPA A2 [] p0 sz0 PS 8 HOME3 P0le P0ge) as [X|X]; [left; exact X| right; left; exact X]. }
    ago AINV3. fold_cl_segs.
    (* [comment removed for export] *)
    shadow_rechk0 SHP3 PS 8.
    zstep. do 4 zstep. zstep. zstep.
    try replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR ST (bv_unsigned sp).
    astop AINV3 MU3 WM3 CFP3.
    pose proof (as_minv LPA A2 _ _ AINV4) as [_ MH4].
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 mx mdx) end;
      [ assumption | assumption | | | | rewrite TCR3, TCR1; reflexivity | rewrite NL3, NL1; clear; lia | rewrite SCR3, SCR1; reflexivity | rewrite PCR3, PCR1; reflexivity (* [comment removed for export] *) | exact ST | assumption | exact DEADS
      | rewrite (LIVEq3 _ (fun E => VNE (eq_sym E))); exact DEADb
      | intros q Q1 Q2; rewrite (LIVEq3 q Q1); apply LIVEq1, Q2 | ].
    { eapply amd_frame_sbm_l; [exact SBM | exact MH |].
      eapply amd_frame_trans; [exact MDF1|]. eapply amd_frame_sbm_l; [exact SBM0 | exact (proj2 (as_minv LPA A1 _ _ AINV1)) |].
      eapply amd_frame_trans; [exact MDF3|]. eapply amd_frame_sbm; [exact SBM1 | exact (proj2 (as_minv LPA A2 _ _ AINV3))]. }
    { intros ff. rewrite FRS3. apply FRS1. }
    { rewrite LBY3, LBY1. lia. }
    lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
      assert (CFb : cframe LPA (owned A1) (owned A2) (bv_unsigned sp) 8224
                       (fun a => newblk S 40 a \/ newblk (vb_buf vr) (vb_size vr) a \/ (PS <= a < PS + 8)) nowhere (aview A1 m2) vfin)
        by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A1 m2) (aview A1 m2) (aview A2 m3) _ [] _);
            [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact FRK3 | lia | lia
            | intros a X; left; exact X | intros a X; destruct X | exact MU3 |
            | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ];
            intros a Ha NO; cbn [outside] in NO; lia);
      eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 m2) vfin CFa CFb); [lia | lia
          | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]
          | intros a X; exact X | intros a X; right; exact X | intros a X; destruct X ]
    end.
  Qed.
End S.
