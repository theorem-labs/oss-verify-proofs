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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpnnp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp.AIcpnl3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.

Module A_VShb8.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_VSe3i A_VSa8f.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, INDENT_STACK in H.
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

  (* [comment removed for export] *)
  Ltac vsb_leaf_call SPEC VSBC VINV0 SHS CE MU STc :=
    icall SPEC
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, INDENT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact STc
                | assumption
                | lia ]);
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STc end.

  Lemma VSB_putc_ok : VSB_putc_stmt.
  Proof.
    unfold VSB_putc_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI A0 VOBJ EM LBY NLV SCM PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite A0. pose proof alloc_ceiling_num as ACV.
    unfold PUTC_STACK, EXT_STACK, ASTK, EXT_MAX in *. unfold VSB_putc_entry.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (vsb_shadows LPA A m md S vr false AINV VOBJ) as [SHS SHB]. fold_cl_segs.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts. unfold vsb_cells in VSBC.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    assert (B8 : vb_buf vr mod 8 = 0) by (apply mod8_of_mod16; exact B16).
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBN. rewrite SHMAX_val in SHBN.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. open_map_cells MC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] |].
      split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf vr), (vb_size vr); split; [exact VLB|lia]| exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 64%nat ST.
    do 9 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep.
    vsb_leaf_call assert_VSB_integrity_ok VSBC VINV0 SHS CE MU ST.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 12.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF end.
    rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
    match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    zstep. zstep. zstep. if_cases K5; zify_cond K5. { dead K5. } clear K5 RDF.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 11.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KE; zify_cond KE.
    - (* [comment removed for export] *)
      exfalso. rewrite Verr in KE. revert KE. vm_compute. first [ intros X; discriminate X | intros X; apply X; reflexivity | congruence ].
    - (* [comment removed for export] *)
      assert (E0 : vb_error vr = 0) by exact Verr.
      clear KE. zstep. zstep.
      vsb_leaf_call vsb_indent_ok VSBC VINV0 SHS CE MU ST.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHS 8. zstep. shadow_chk0 SHS 8.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. if_cases KR; zify_cond KR.
      + (* [comment removed for export] *)
        unsign KR.
        zstep. shadow_chk0 SHS 8. shadow_rechk0 SHS (S + 24) 8.
        zstep. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        shadow_chk SHB 1 12.
        pose proof (u8arr_store_ok rsegs _ _ _ (vb_len vr) _ U8 ltac:(lia) eq_refl) as SOK.
        zstep. rewrite le1_single.
        pose proof (u8arr_write rsegs _ _ _ (vb_len vr) (Z_to_bv 8 (bv_unsigned a1)) U8 ltac:(lia)) as U8'. clear U8. store_done.
        (* [comment removed for export] *)
        zstep. shadow_rechk SHS (S + 4) 4 11.
        zstep. rewrite E0. zstep. zstep. do 8 zstep. zstep. zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        astop AINV MU WM CFP.
        pose proof (as_minv LPA A _ _ AINV) as [_ MH].
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx mdx (vsb_set_len vr (vb_len vr + 1))) end;
          [ assumption | assumption | eapply amd_frame_sbm; [exact SBM| exact MH] |
          | cbn [vsb_set_len vb_len]; lia | cbn [vsb_set_len vb_size vb_len]; lia
          | left; reflexivity (* [comment removed for export] *)
          | intros q _ _; reflexivity | left; reflexivity | intros ff; reflexivity
          | cbn [vsb_set_len vb_size]; lia | reflexivity | reflexivity | unfold vsb_pot; cbn [vb_size vsb_set_len]; lia
          | unfold vsb_ppot; cbn [vb_size vsb_set_len]; lia (* [comment removed for export] *) | exact ST | ].
        * split; [exact VSBC|]. split; [unfold vsb_inv; cbn [vsb_set_len vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|].
          split; [exact VLS|]. split; [exact VLB|]. split; [exact VNE|].
          eexists. split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vb_size vb_len]; lia| intros X; discriminate X].
        * cbn [vsb_set_len vb_buf vb_size].
          eapply (cframe_noalloc LPA); [exact MU | | | intros a X; left; exact X].
          -- intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
          -- eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia].
      + (* [comment removed for export] *)
        unsign KR.
        zstep. zstep. zstep.
        astop AINV MU WM CFP. fold_cl_segs.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 64) 64 AINV0 ltac:(lia) ltac:(lia)
                        (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF end.
        pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
        pose proof (VSB_extend_ok) as HEXT. unfold VSB_extend_stmt in HEXT.
        eapply HEXT;
          [ exact AINV0 | assumption | reflexivity | reflexivity
          | split; [exact VSBC|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
            exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
          | lia | unfold EXT_MAX; lia | exact LBY | exact NLV | intros _; exact SCM | apply prim_room_ext; [lia| exact PCM] (* [comment removed for export] *) | exact TP
          | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
          | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, ASTK; lia
          | ].
        clear HEXT VSBC U8 SHS SHB.
        intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' vr'. cbv zeta.
        intros AINV' MI' MDF VOBJ' LIVEq FRS TCR NLV' ST' OUT.
        fold_cl_segs. fold_aview. rewrite unsigned_lit in OUT, ST' by lia. unfold EXT_STACK, ASTK in OUT.
        (first [ pose proof ((vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ')) as dR_4; dand11 dR_4 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
        pose proof (vsb_shadows LPA A' m' md' S vr' false AINV' VOBJ') as [SHS' SHB']. fold_cl_segs. fold_aview.
        unfold kHighMemBeg in Blo'. all_app_facts.
        pose proof VOBJ' as VOBJ1. vsb_open VOBJ'. (first [ dex1 VBUF as bs1; dand3 VBUF as U8n LBS1 _ | dand4 VBUF as bs1 U8n LBS1 _ | destruct VBUF as (bs1 & U8n & LBS1 & _) ]).
        pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
        unfold vsb_cells in VSBC.
        pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr') (vb_size vr') ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB'. rewrite SHMAX_val in SHBB'.
        pose proof (as_minv LPA A' _ _ AINV') as [_ MH'].
        destruct OUT as (nb & Er & Ev & COPY & FRESH & REL & LBY' & SCR & PCR & FRK); subst r.   (* [comment removed for export] *)
        (* [comment removed for export] *)
        * (* [comment removed for export] *)
          subst vr'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in *.
          (first [ pose proof ((vsb_extendsize_spec (vb_size vr + 1) ltac:(lia))) as dR_7; dand3 dR_7 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size vr + 1) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
          pose proof (vsb_extendsize_tight (vb_size vr + 1)) as NS4.
          clear ST. acall_xfer FRK. rename ST' into ST.
          assert (NB8 : nb mod 8 = 0) by (apply mod8_of_mod16; exact B16').
          pose proof (munch_refl [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (nb, nb + vsb_extendsize (vb_size vr + 1))] (aview A' m')) as MU2.
          pose proof (wmono_refl rsegs (aview A' m')) as WM2.
          assert (WMAP2 : mapped (aview A' m') (bv_unsigned sp - 8336) 8336).
          { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
          assert (CFP2 : client_fp LPA A' (aview A' m') [(bv_unsigned sp - 8336, bv_unsigned sp); (S, S + 40); (nb, nb + vsb_extendsize (vb_size vr + 1))]).
          { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8336)) with 8336 by lia; exact WMAP2 |].
            split; [right; left; exists S, 40; split; [exact VLS0|lia]|].
            split; [right; left; eexists _, _; split; [exact VLB0| lia]| exact I]. }
          ago AINV'. fold_cl_segs. fix_ret_pc.
          zstep. if_cases KX; zify_cond KX. { dead KX. } clear KX.
          (* [comment removed for export] *)
          shadow_rechk SHS' (S + 4) 4 11.
          zstep. rewrite E0. zstep. if_cases KY; zify_cond KY. { exfalso. revert KY. vm_compute. congruence. } clear KY.
          (* [comment removed for export] *)
          zstep. shadow_chk0 SHS' 8. shadow_rechk0 SHS' (S + 24) 8.
          zstep. zstep. zstep. zstep. zstep.
          (* [comment removed for export] *)
          shadow_chk SHB' 1 12.
          pose proof (u8arr_store_ok rsegs _ _ _ (vb_len vr) _ U8n ltac:(lia) eq_refl) as SOK.
          zstep. rewrite le1_single.
          pose proof (u8arr_write rsegs _ _ _ (vb_len vr) (Z_to_bv 8 (bv_unsigned a1)) U8n ltac:(lia)) as U8'. clear U8n. store_done.
          (* [comment removed for export] *)
          zstep. shadow_rechk SHS' (S + 4) 4 11.
          zstep. rewrite E0. zstep. zstep. do 8 zstep. zstep. zstep.
          try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
          release_frame FR ST (bv_unsigned sp).
          astop AINV' MU2 WM2 CFP2.
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
            eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mx mdx
                      (vsb_set_len (vsb_set_buf_size vr nb (vsb_extendsize (vb_size vr + 1))) (vb_len vr + 1))) end;
            [ assumption | assumption | | | cbn [vsb_set_len vsb_set_buf_size vb_len]; lia
            | cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; lia
            | right; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; split; [lia| reflexivity] (* [comment removed for export] *)
            | exact LIVEq | right; cbn [vsb_set_len vsb_set_buf_size vb_buf]; split; [exact FRESH| exact REL] | exact FRS
            | cbn [vsb_set_len vsb_set_buf_size vb_size]; lia
            | exact TCR | exact NLV'
            | pose proof (vsb_pot_credit _ _ vr nb 1 ltac:(try (generalize alloc_ceiling_val); clear - VINV0; try pose proof alloc_ceiling_val as ACV__; unfold vsb_inv in VINV0; lia) ltac:(lia) SCR) as PC;
              unfold vsb_pot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; try (generalize alloc_ceiling_val); clear - PC; try pose proof alloc_ceiling_val as ACV__; lia
            | pose proof (vsb_ppot_credit _ _ vr nb 1 ltac:(clear - VINV0; unfold vsb_inv in VINV0; lia) ltac:(clear; lia) PCR) as PP;
              unfold vsb_ppot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; clear - PP; lia (* [comment removed for export] *)
            | exact ST | ].
          -- eapply amd_frame_sbm_l; [exact SBM | exact MH |]. eapply amd_frame_sbm_r; [exact MDF | eassumption].
          -- split; [exact VSBC|].
             split; [unfold vsb_inv; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf];
                    unfold vsb_inv in VINV1; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_buf_size] in VINV1; lia|].
             split; [exact VLS0|]. split; [exact VLB0|]. split; [exact VNE0|].
             eexists; split; [exact U8'|]. split; [rewrite upd_length; cbn [vsb_set_len vsb_set_buf_size vb_size]; lia| intros X; discriminate X].
          -- cbn [vsb_set_len vsb_set_buf_size vb_buf vb_size].
             lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
             eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A' m') vfin _ _);
               [ exact MU | | exact FRK | lia | lia | intros a X; exact X
               | intros a X; left; exact X
               | exact MU2 | | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ] end.
             ++ intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
             ++ intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
  Qed.
End S.
End A_VShb8.

   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
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
Definition bcat_hid (P : Prop) : Prop := P.
Local Ltac bcat_hide_hyp H := lazymatch type of H with ?T => change (bcat_hid T) in H end.
Local Ltac bcat_unhide_all := repeat match goal with H : bcat_hid _ |- _ => unfold bcat_hid in H end.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Po6qc A_Vsb A_World A_Img A_Cocsh A_VSe3i A_VSa8f.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.lia0_first := Ltac2.Init.true.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold vsb_leaf_post, leaf_post, ASSERT_STACK, INDENT_STACK, asan_memcpy_post, ASAN_MEMCPY_STACK in H.

(* [comment removed for export] *)
Lemma vsb_dbl_ge_ns : forall k ns sz, 0 < ns -> ns <= vsb_dbl k ns sz.
Proof.
  induction k as [|k IH]; intros ns sz Hns; cbn [vsb_dbl]; [lia|].
  destruct (Z.ltb ns sz); [|lia]. specialize (IH (2 * ns) sz ltac:(lia)). lia.
Qed.
Lemma vsb_dbl_mono : forall k ns s1 s2, 0 < ns -> s1 <= s2 -> vsb_dbl k ns s1 <= vsb_dbl k ns s2.
Proof.
  induction k as [|k IH]; intros ns s1 s2 Hns Hs; cbn [vsb_dbl]; [lia|].
  destruct (Z.ltb_spec ns s1) as [L1|G1]; destruct (Z.ltb_spec ns s2) as [L2|G2]; try lia.
  - apply IH; lia.
  - pose proof (vsb_dbl_ge_ns k (2 * ns) s2 ltac:(lia)). lia.
Qed.
Lemma vsb_extendsize_mono : forall a b, a <= b -> vsb_extendsize a <= vsb_extendsize b.
Proof.
  intros a b Hab. unfold vsb_extendsize.
  destruct (Z.ltb_spec a 4096) as [La|Ga]; destruct (Z.ltb_spec b 4096) as [Lb|Gb]; try lia.
  - apply vsb_dbl_mono; lia.
  - eapply Z.le_trans with (m := vsb_dbl 9 16 4096).
    + apply vsb_dbl_mono; lia.
    + change (vsb_dbl 9 16 4096) with 4096. Z.div_mod_to_equations. nia.
  - Z.div_mod_to_equations. nia.
Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Ltac vsb_leaf_call SPEC VSBC VINV0 SHS CE MU STc :=
    icall SPEC
      by (try rewrite unsigned_lit by lia; unfold ASSERT_STACK, INDENT_STACK, kHighMemBeg;
          first [ reflexivity
                | exact VSBC
                | exact VINV0
                | (eexists _, _; split; [exact SHS| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia])
                | (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                | exact STc
                | assumption
                | lia ]);
    lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into STc end.

  (* [comment removed for export] *)
  Ltac bcat_epilogue FR ST sp :=
    zstep; do 10 zstep; zstep; zstep;
    try replace (bv_unsigned sp + -80 + 80) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    release_frame FR ST (bv_unsigned sp).

  #[using="AI16"] Lemma VSB_bcat_ok : VSB_bcat_stmt.
  Proof.
    unfold VSB_bcat_stmt, frames_same.
    intros until T. cbv zeta. intros AINV MI A0 A1 A2 VOBJ BSRC LSRC CO EM LBY NLV SCM PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite A0, A1, A2. pose proof alloc_ceiling_num as ACV.
    unfold BCAT_STACK, EXT_STACK, ASTK, EXT_MAX in *. unfold VSB_bcat_entry.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    (first [ pose proof ((vsb_obj_geom LPA A m md S vr false AINV VOBJ)) as dR_1; dand11 dR_1 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A m md S vr false AINV VOBJ) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    pose proof (vsb_shadows LPA A m md S vr false AINV VOBJ) as [SHS SHB]. fold_cl_segs.
    pose proof VOBJ as VOBJ0. vsb_open VOBJ. (first [ dex1 VBUF as bs0; dand3 VBUF as U8 LBS _ | dand4 VBUF as bs0 U8 LBS _ | destruct VBUF as (bs0 & U8 & LBS & _) ]). pose proof VINV as VINV0.
    (first [ dand8 VINV as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | destruct VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    unfold vsb_cells in VSBC.
    assert (S8 : S mod 8 = 0) by (apply mod8_of_mod16; exact S16).
    assert (B8 : vb_buf vr mod 8 = 0) by (apply mod8_of_mod16; exact B16).
    pose proof (shpat_sh_boundL (Clg:=Clg) S 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHSB. rewrite SHMAX_val in SHSB.
    pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB. rewrite SHMAX_val in SHBB.
    pose proof (sh_boundL (Clg:=Clg) (vb_buf vr) (vb_size vr) ltac:(lia) ltac:(lia) ltac:(lia)) as SHBN. rewrite SHMAX_val in SHBN.
    pose proof (bytes_at_bound _ _ _ _ BSRC) as SRCB.
    (* [comment removed for export] *)
    (first [ pose proof ((cobj_open (Clg:=Clg) LPA A m md _ SRC (Z.of_nat (length src)) AINV CO ltac:(lia))) as dR_4; dex2 dR_4 as p0 sz0; dand9 dR_4 as SHP P08 P0lo P0le P0ge P0ce HOME CRP PDJ | pose proof ((cobj_open (Clg:=Clg) LPA A m md _ SRC (Z.of_nat (length src)) AINV CO ltac:(lia))) as dR_4; dand11 dR_4 as p0 sz0 SHP P08 P0lo P0le P0ge P0ce HOME CRP PDJ | destruct (cobj_open (Clg:=Clg) LPA A m md _ SRC (Z.of_nat (length src)) AINV CO ltac:(lia)) as (p0 & sz0 & SHP & P08 & P0lo & P0le & P0ge & P0ce & HOME & CRP & PDJ) ]).
    fold_cl_segs. unfold kHighMemBeg in P0lo. all_app_facts. clear CRP.
    pose proof (shpat_sh_boundL (Clg:=Clg) p0 sz0 ltac:(lia) ltac:(lia) ltac:(lia)) as SHPB. rewrite SHMAX_val in SHPB.
    pose proof (conj SHP I) as SHP0.   (* [comment removed for export] *)
    assert (PSS : SRC + Z.of_nat (length src) <= S \/ S + 40 <= SRC)
      by (destruct (PDJ S 40 VLS ltac:(cbn; tauto)); lia).
    assert (PSB : SRC + Z.of_nat (length src) <= vb_buf vr \/ vb_buf vr + vb_size vr <= SRC)
      by (destruct (PDJ (vb_buf vr) (vb_size vr) VLB ltac:(cbn; tauto)); lia).
    clear PDJ.
    pose proof (cenv_intro A m md AINV) as CE.
    pose proof (map_cells_of_consts _ (proj1 CE)) as MC. open_map_cells MC.
    pose proof (rw_cells_bound _ _ _ _ VSBC) as SB. cbn [cells_size csize Nat.add length] in SB.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (vb_buf vr, vb_buf vr + vb_size vr)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] |].
      split; [right; left; exists S, 40; split; [exact VLS|lia]|].
      split; [right; left; exists (vb_buf vr), (vb_size vr); split; [exact VLB|lia]| exact I]. }
    ago AINV. fold_cl_segs.
    carve_frame 80%nat ST.
    do 11 zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    vsb_leaf_call assert_VSB_integrity_ok VSBC VINV0 SHS CE MU ST.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 12.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 34 1 VSBC ltac:(lia) ltac:(cbn; lia)) as RDF end.
    rewrite Vfl in RDF. unfold VSB_FLAGS_LIVE in RDF.
    match type of RDF with _ = Some ?r => let r' := eval vm_compute in r in change r with r' in RDF end.
    zstep. zstep. zstep. if_cases K5; zify_cond K5. { dead K5. } clear K5 RDF.
    (* [comment removed for export] *)
    zstep. if_cases K6; zify_cond K6. { dead K6. } clear K6.
    (* [comment removed for export] *)
    zstep. shadow_chk SHS 4 11.
    zstep. zstep. zstep. if_cases KE; zify_cond KE.
    2:{ (* [comment removed for export] *)
        exfalso. rewrite Verr in KE. revert KE. vm_compute. first [ intros X; discriminate X | intros X; apply X; reflexivity | congruence ]. }
    (* [comment removed for export] *)
    assert (E0 : vb_error vr = 0) by exact Verr.
    clear KE.
    (* [comment removed for export] *)
    zstep. if_cases KL; zify_cond KL. { dead KL. } clear KL.
    zstep. zstep.
    vsb_leaf_call vsb_indent_ok VSBC VINV0 SHS CE MU ST.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHS 8. zstep. shadow_chk0 SHS 8.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    rewrite (lxor_ones (vb_len vr)) by lia.
    wrap_reg (vb_size vr + (18446744073709551615 - vb_len vr)) (vb_size vr - vb_len vr - 1).
    zstep. if_cases KR; zify_cond KR; unsign KR.
    - (* [comment removed for export] *)
      zstep. shadow_chk0 SHS 8. shadow_rechk0 SHS (S + 24) 8.
      zstep. zstep. zstep. zstep. zstep.
      (first [ pose proof ((u8arr_window rsegs _ _ _ (Z.to_nat (vb_len vr)) (length src) U8 ltac:(lia))) as dR_5; dand3 dR_5 as U8a U8b U8c | destruct (u8arr_window rsegs _ _ _ (Z.to_nat (vb_len vr)) (length src) U8 ltac:(lia)) as (U8a & U8b & U8c) ]).
      pose proof (rw_cells_of_u8arr rsegs _ _ _ U8b) as DST. clear U8b U8.
      rewrite Z2Nat.id in DST, U8c by lia.
      rewrite firstn_length_le in DST by (rewrite skipn_length; lia).
      assert (LA : length (firstn (Z.to_nat (vb_len vr)) bs0) = Z.to_nat (vb_len vr)) by (rewrite firstn_length_le; lia).
      assert (LC : length (skipn (Z.to_nat (vb_len vr) + length src) bs0) = (length bs0 - (Z.to_nat (vb_len vr) + length src))%nat)
        by (rewrite skipn_length; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (CEc : cenv mx) by (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]);
        pose proof (asan_memcpy_cells_of_consts _ (proj1 CEc)) as AMC;
        assert (RS : range_ok mx SRC (Z.of_nat (length src)))
          by (eapply range_ok_high_munch; [ eapply (chome_range_ok A m md _ p0 sz0); [exact AINV| exact HOME| exact (proj1 SHP0)| exact P08| lia| exact P0le| exact P0ge| lia]
                                           | exact MU| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia]);
        assert (RD : range_ok mx (vb_buf vr + vb_len vr) (Z.of_nat (length src)))
          by (eapply range_ok_high_munch; [ eapply live_range_ok; [exact AINV| exact VLB| lia| lia| lia]
                                           | exact MU| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia])
      end.
      zstep. icall asan_memcpy_spec by
        (rewrite ?unsigned_lit by lia;
         first [ exact BSRC | (rewrite Nat2Z.id; reflexivity) | (rewrite Nat2Z.id; exact DST) | exact AMC | exact ST | exact CEIL
               | (right; split; [exact RS| exact RD])
               | (unfold ASAN_MEMCPY_STACK; lia) | (left; lia) | lia | assumption ]).
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      (* [comment removed for export] *)
      match goal with H : rw_cells rsegs ?mx (vb_buf vr + vb_len vr) [CB _ src] |- _ =>
        rewrite Nat2Z.id in H; pose proof (u8arr_of_rw_cells rsegs _ _ _ _ H) as U8b; clear H end.
      match goal with Ha : u8arr rsegs ?mx (vb_buf vr) ?pre, Hc : u8arr rsegs ?mx (vb_buf vr + vb_len vr + _) ?post |- _ =>
        pose proof (u8arr_unwindow rsegs mx (vb_buf vr) pre src post Ha
                      ltac:(rewrite LA, Z2Nat.id by lia; exact U8b)
                      ltac:(rewrite LA, Z2Nat.id by lia; exact Hc)) as U8n; clear Ha Hc U8b end.
      assert (LBn : Z.of_nat (length (firstn (Z.to_nat (vb_len vr)) bs0 ++ src ++ skipn (Z.to_nat (vb_len vr) + length src) bs0)) = vb_size vr)
        by (rewrite !app_length, LA, LC; lia).
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep.
      bcat_epilogue FR ST sp.
      astop AINV MU WM CFP.
      pose proof (as_minv LPA A _ _ AINV) as [_ MH].
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
        eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx mdx (vsb_set_len vr (vb_len vr + Z.of_nat (length src)))) end;
        [ assumption | assumption | eapply amd_frame_sbm; [exact SBM| exact MH] |
        | cbn [vsb_set_len vb_len]; lia | cbn [vsb_set_len vb_size vb_len]; lia
        | intros q _ _; reflexivity | left; reflexivity | intros ff; reflexivity
        | cbn [vsb_set_len vb_size]; lia | reflexivity | reflexivity | unfold vsb_pot; cbn [vb_size vsb_set_len]; lia
        | unfold vsb_ppot; cbn [vb_size vsb_set_len]; lia (* [comment removed for export] *) | exact ST | ].
      { split; [exact VSBC|]. split; [unfold vsb_inv; cbn [vsb_set_len vb_size vb_len vb_error vb_indent vb_flags vb_buf]; lia|].
        split; [exact VLS|]. split; [exact VLB|]. split; [exact VNE|].
        eexists. split; [exact U8n|]. split; [rewrite LBn; cbn [vsb_set_len vb_size]; lia| intros X; discriminate X]. }
      cbn [vsb_set_len vb_buf vb_size].
      eapply (cframe_noalloc LPA); [exact MU | | | intros a X; left; exact X].
      + intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. lia.
      + eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 80) 80 AINV0 ltac:(lia) ltac:(lia)
                      (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CF;
        pose proof (chome_crange (Clg:=Clg) LPA A _ _ _ p0 sz0 SRC (Z.of_nat (length src)) AINV0 HOME P0le P0ge ltac:(lia)) as CRS end.
      pose proof (as_minv LPA A _ _ AINV) as [_ MH]. pose proof (as_minv LPA A _ _ AINV0) as [_ MH0].
      pose proof (VSB_extend_ok) as HEXT. unfold VSB_extend_stmt in HEXT.
      eapply HEXT;
        [ exact AINV0 | assumption | reflexivity | reflexivity
        | split; [exact VSBC|]; split; [exact VINV0|]; split; [exact VLS|]; split; [exact VLB|]; split; [exact VNE|];
          exists bs0; split; [exact U8|]; split; [exact LBS| intros X; discriminate X]
        | lia | unfold EXT_MAX; lia
        | eapply Z.le_trans; [| exact LBY]; apply Z.add_le_mono_l; apply vsb_extendsize_mono; lia
        | exact NLV | intros _; exact SCM
        | apply prim_room_ext; [lia| exact PCM] (* [comment removed for export] *)
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold EXT_STACK, ASTK; lia
        | ].
      clear HEXT VSBC U8 SHS SHB.
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' vr'. cbv zeta.
      intros AINV' MI' MDF VOBJ' LIVEq FRS TCR NLV' ST' OUT.
      fold_cl_segs. fold_aview. rewrite unsigned_lit in OUT, ST' by lia. unfold EXT_STACK, ASTK in OUT.
      (first [ pose proof ((vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ')) as dR_6; dand11 dR_6 as _ _ _ _ B16' Blo' Bhi' Bimg' DSB' Smap' Bmap' | pose proof (vsb_obj_geom LPA A' m' md' S vr' false AINV' VOBJ') as (_ & _ & _ & _ & B16' & Blo' & Bhi' & Bimg' & DSB' & Smap' & Bmap') ]).
      pose proof (vsb_shadows LPA A' m' md' S vr' false AINV' VOBJ') as [SHS' SHB']. fold_cl_segs. fold_aview.
      unfold kHighMemBeg in Blo'. all_app_facts.
      pose proof VOBJ' as VOBJ1. vsb_open VOBJ'. (first [ dex1 VBUF as bs1; dand3 VBUF as U8n LBS1 _ | dand4 VBUF as bs1 U8n LBS1 _ | destruct VBUF as (bs1 & U8n & LBS1 & _) ]).
      pose proof VINV as VINV1. (first [ dand8 VINV as Vsz' Vlen' Verr' Vind' Vfl' Vb0' Vb47' Vbm' | destruct VINV as (Vsz' & Vlen' & Verr' & Vind' & Vfl' & Vb0' & Vb47' & Vbm') ]).
      unfold vsb_cells in VSBC.
      pose proof (shpat_sh_boundL (Clg:=Clg) (vb_buf vr') (vb_size vr') ltac:(lia) ltac:(lia) ltac:(lia)) as SHBB'. rewrite SHMAX_val in SHBB'.
      pose proof (as_minv LPA A' _ _ AINV') as [_ MH'].
      destruct OUT as (nb & Er & Ev & COPY & FRESH & REL & LBY' & SCR & PCR & FRK); subst r.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      + (* [comment removed for export] *)
        subst vr'. cbn [vb_buf vb_size vb_len vb_error vb_flags vb_indent vsb_set_buf_size] in *.
        (first [ pose proof ((vsb_extendsize_spec (vb_size vr + (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1))) ltac:(lia))) as dR_9; dand3 dR_9 as NS1 NS2 NS3 | pose proof (vsb_extendsize_spec (vb_size vr + (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1))) ltac:(lia)) as (NS1 & NS2 & NS3) ]).
          pose proof (vsb_extendsize_tight (vb_size vr + (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1)))) as NS4.
        remember (vsb_extendsize (vb_size vr + (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1)))) as ns eqn:Ens.
        assert (NE' : S <> nb) by exact VNE0.
        destruct (chome_call (Clg:=Clg) LPA A A' _ _ m' md' _ _ _ _ _ _ [S; nb] p0 sz0 AINV0 HOME SHP ltac:(lia) FRK ltac:(lia)) as [SHP' HOME'];
          [ intros p k LP NI; split; [rewrite LIVEq; [exact LP| intros ->; apply NI; cbn; tauto| intros ->; rewrite FRESH in LP; discriminate]
                                   | cbn; intros [X|[X|X]]; [apply NI; cbn; tauto| subst p; rewrite FRESH in LP; discriminate| exact X] ]
          | intros ff kk age HF; rewrite FRS; exact HF
          | intros xv ff kk age [X|X] HF; [ eapply (newblk_avoids_fshadow LPA A _ _ (vb_buf vr) (vb_size vr)); [exact AINV0| exact VLB| exact HF| exact X]
                                          | eapply (high_avoids_fshadow LPA A _ _ ff kk age xv AINV0 HF); unfold OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9.inmem_range, kHighMemBeg; lia ]
          | exact AINV' | reflexivity | ].
        (* [comment removed for export] *)
        pose proof (newblock_cdisjoint (Clg:=Clg) LPA A A' _ _ _ _ _ _ FRK nb ns SRC (Z.of_nat (length src))
                      ltac:(intros xq Hxq; left; split; lia) CRS
                      ltac:(split; [left; lia| intros i Hi X; unfold newblk, blk in X; clear - Blo P0le P0ge P0lo PSS PSB Hi X; lia])) as DNB0.   (* [comment removed for export] *)
        assert (DNB : SRC + Z.of_nat (length src) <= nb \/ nb + ns <= SRC) by (clear - LSRC Vlen' DNB0; lia). clear DNB0.
        clear SHP HOME ST. try clear Gsh. try clear Csh. try clear Gmb. try clear Cmb. try clear Gme. try clear Cme. try clear Ghe. try clear Che. acall_xfer FRK. rename ST' into ST.
        assert (NB8 : nb mod 8 = 0) by (apply mod8_of_mod16; exact B16').
        pose proof (sh_boundL (Clg:=Clg) nb ns ltac:(lia) ltac:(lia) ltac:(lia)) as SHBN'. rewrite SHMAX_val in SHBN'.
        pose proof (munch_refl [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (nb, nb + ns)] (aview A' m')) as MU2.
        pose proof (wmono_refl rsegs (aview A' m')) as WM2.
        assert (WMAP2 : mapped (aview A' m') (bv_unsigned sp - 8352) 8352).
        { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
        assert (CFP2 : client_fp LPA A' (aview A' m') [(bv_unsigned sp - 8352, bv_unsigned sp); (S, S + 40); (nb, nb + ns)]).
        { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8352)) with 8352 by lia; exact WMAP2 |].
          split; [right; left; exists S, 40; split; [exact VLS0|lia]|].
          split; [right; left; eexists _, _; split; [exact VLB0| lia]| exact I]. }
        (* [comment removed for export] *)
        pose proof (chome_range_ok (Clg:=Clg) A' m' md' _ p0 sz0 SRC (Z.of_nat (length src)) AINV' HOME' SHP' P08 ltac:(lia) P0le P0ge ltac:(lia)) as RS0.
        pose proof (live_range_ok (Clg:=Clg) A' m' md' nb ns (nb + vb_len vr) (Z.of_nat (length src)) AINV' VLB0 ltac:(lia) ltac:(lia) ltac:(lia)) as RD0.
        fold_aview. pose proof (conj RS0 RD0) as RNG0. clear RS0 RD0.
        pose proof (cenv_intro A' m' md' AINV') as CE'.
        ago AINV'. fold_cl_segs. fix_ret_pc.
        zstep. if_cases KX; zify_cond KX. { dead KX. } clear KX.
        (* [comment removed for export] *)
        shadow_rechk SHS' (S + 4) 4 11.
        zstep. rewrite E0. zstep. if_cases KY; zify_cond KY. { exfalso. revert KY. vm_compute. congruence. } clear KY.
        (* [comment removed for export] *)
        zstep. shadow_chk0 SHS' 8. shadow_rechk0 SHS' (S + 24) 8.
        zstep. zstep. zstep. zstep. zstep.
        (first [ pose proof ((u8arr_window rsegs _ _ _ (Z.to_nat (vb_len vr)) (length src) U8n ltac:(lia))) as dR_10; dand3 dR_10 as U8a U8b U8c | destruct (u8arr_window rsegs _ _ _ (Z.to_nat (vb_len vr)) (length src) U8n ltac:(lia)) as (U8a & U8b & U8c) ]).
        pose proof (rw_cells_of_u8arr rsegs _ _ _ U8b) as DST. clear U8b U8n.
        rewrite Z2Nat.id in DST, U8c by lia.
        rewrite firstn_length_le in DST by (rewrite skipn_length; lia).
        assert (LA : length (firstn (Z.to_nat (vb_len vr)) bs1) = Z.to_nat (vb_len vr)) by (rewrite firstn_length_le; lia).
        assert (LC : length (skipn (Z.to_nat (vb_len vr) + length src) bs1) = (length bs1 - (Z.to_nat (vb_len vr) + length src))%nat)
          by (rewrite skipn_length; lia).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          assert (CEc : cenv mx) by (eapply cenv_munch; [exact CE'| exact MU2| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]);
          pose proof (asan_memcpy_cells_of_consts _ (proj1 CEc)) as AMC;
          assert (RS : range_ok mx SRC (Z.of_nat (length src)))
            by (eapply range_ok_high_munch; [ exact (proj1 RNG0) | exact MU2| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia]);
          assert (RD : range_ok mx (nb + vb_len vr) (Z.of_nat (length src)))
            by (eapply range_ok_high_munch; [ exact (proj2 RNG0) | exact MU2| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia])
        end.
        (* [comment removed for export] *)
        assert (UL1 : bv_unsigned (Z_to_bv 64 SRC) = SRC) by (apply unsigned_lit; clear - SRCB LSRC; lia).
        assert (UL2 : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; clear - LSRC; lia).
        assert (UL3 : bv_unsigned (Z_to_bv 64 (nb + vb_len vr)) = nb + vb_len vr) by (apply unsigned_lit; clear - Vb0' Vlen' Vb47'; lia).
        assert (UL4 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - SPR LO LO0; lia).
        try bcat_hide_hyp Verr; try bcat_hide_hyp Verr'; try bcat_hide_hyp DSB; try bcat_hide_hyp PSB; try bcat_hide_hyp PSS; try bcat_hide_hyp Vbm; try bcat_hide_hyp S16;
        try bcat_hide_hyp B16; try bcat_hide_hyp B8; try bcat_hide_hyp S8; try bcat_hide_hyp SP16; try bcat_hide_hyp P08; try bcat_hide_hyp NB8; try bcat_hide_hyp NS3;
        try bcat_hide_hyp Vbm'; try bcat_hide_hyp B16'; try bcat_hide_hyp SHSB; try bcat_hide_hyp SHBB; try bcat_hide_hyp SHBN; try bcat_hide_hyp SHPB; try bcat_hide_hyp SHBB';
        try bcat_hide_hyp SHBN'; try bcat_hide_hyp NS4; try bcat_hide_hyp V16C; try bcat_hide_hyp V16C0; try bcat_hide_hyp Vb47; try bcat_hide_hyp Vb0; try bcat_hide_hyp Bhi;
        try bcat_hide_hyp Vsz; try bcat_hide_hyp LBS; try bcat_hide_hyp EM; try bcat_hide_hyp LBY; try bcat_hide_hyp NLV; try bcat_hide_hyp SCM; try bcat_hide_hyp PCM; try bcat_hide_hyp TCR;
        try bcat_hide_hyp NLV'; try bcat_hide_hyp LBY'; try bcat_hide_hyp SCR; try bcat_hide_hyp PCR; try bcat_hide_hyp Vlen; try bcat_hide_hyp DNB0.
        zstep. try clear SHP'. try clear SHB'. try clear SHS'. icall asan_memcpy_spec by
          (rewrite ?UL1, ?UL2, ?UL3, ?UL4;
           first [ exact BSRC | (rewrite Nat2Z.id; reflexivity) | (rewrite Nat2Z.id; exact DST) | exact AMC | exact ST | exact CEIL
                 | (right; split; [exact RS| exact RD])
                 | (unfold ASAN_MEMCPY_STACK; clear - LO; lia)
                 | (left; clear - Bhi' CEIL NS1 Vlen' P0ge P0ce; lia)
                 | (clear - DNB Vlen' NS1 LSRC; lia)
                 | (rewrite ?unsigned_lit by lia; first [ (unfold ASAN_MEMCPY_STACK; lia) | (left; lia) | lia | assumption ]) ]).
        clear UL1 UL2 UL3 UL4.
        bcat_unhide_all.
        lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
        match goal with H : rw_cells rsegs ?mx (nb + vb_len vr) [CB _ src] |- _ =>
          rewrite Nat2Z.id in H; pose proof (u8arr_of_rw_cells rsegs _ _ _ _ H) as U8b; clear H end.
        match goal with Ha : u8arr rsegs ?mx nb ?pre, Hc : u8arr rsegs ?mx (nb + vb_len vr + _) ?post |- _ =>
          pose proof (u8arr_unwindow rsegs mx nb pre src post Ha
                        ltac:(rewrite LA, Z2Nat.id by lia; exact U8b)
                        ltac:(rewrite LA, Z2Nat.id by lia; exact Hc)) as U8f; clear Ha Hc U8b end.
        assert (LBn : Z.of_nat (length (firstn (Z.to_nat (vb_len vr)) bs1 ++ src ++ skipn (Z.to_nat (vb_len vr) + length src) bs1)) = ns)
          by (rewrite !app_length, LA, LC; lia).
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        bcat_epilogue FR ST sp.
        astop AINV' MU2 WM2 CFP2.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A' mx mdx
                    (vsb_set_len (vsb_set_buf_size vr nb ns) (vb_len vr + Z.of_nat (length src)))) end;
          [ assumption | assumption | | | cbn [vsb_set_len vsb_set_buf_size vb_len]; lia
          | cbn [vsb_set_len vsb_set_buf_size vb_size vb_len]; lia
          | exact LIVEq | right; cbn [vsb_set_len vsb_set_buf_size vb_buf]; split; [exact FRESH| exact REL] | exact FRS
          | cbn [vsb_set_len vsb_set_buf_size vb_size]; lia
          | exact TCR | exact NLV'
          | subst ns; pose proof (vsb_pot_credit _ _ vr nb (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1)) ltac:(try (generalize alloc_ceiling_val); clear - VINV0; try pose proof alloc_ceiling_val as ACV__; unfold vsb_inv in VINV0; lia) ltac:(lia) SCR) as PC;
            unfold vsb_pot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; try (generalize alloc_ceiling_val); clear - PC; try pose proof alloc_ceiling_val as ACV__; lia
          | subst ns; pose proof (vsb_ppot_credit _ _ vr nb (Z.of_nat (length src) - (vb_size vr - vb_len vr - 1)) ltac:(clear - VINV0; unfold vsb_inv in VINV0; lia) ltac:(lia) PCR) as PP;
            unfold vsb_ppot in *; cbn [vb_size vsb_set_len vsb_set_buf_size] in *; clear - PP; lia (* [comment removed for export] *)
          | exact ST | ].
        * eapply amd_frame_sbm_l; [exact SBM | exact MH |]. eapply amd_frame_sbm_r; [exact MDF | eassumption].
        * split; [exact VSBC|].
          split; [unfold vsb_inv; cbn [vsb_set_len vsb_set_buf_size vb_size vb_len vb_error vb_indent vb_flags vb_buf];
                 unfold vsb_inv in VINV1; cbn [vb_size vb_len vb_error vb_indent vb_flags vb_buf vsb_set_buf_size] in VINV1; lia|].
          split; [exact VLS0|]. split; [exact VLB0|]. split; [exact VNE0|].
          eexists; split; [exact U8f|]. split; [rewrite LBn; cbn [vsb_set_len vsb_set_buf_size vb_size]; lia| intros X; discriminate X].
        * cbn [vsb_set_len vsb_set_buf_size vb_buf vb_size].
          lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
          eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A' m') vfin _ _);
            [ exact MU | | exact FRK | lia | lia | intros a X; exact X
            | intros a X; left; exact X
            | exact MU2 | | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ] end.
          -- intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. clear - Vb0 NO. lia.   (* [comment removed for export] *)
          -- intros a Ha NO. cbn [outside] in NO. unfold newblk, blk. clear - Vb0' LBn Ha NO. lia.   (* [comment removed for export] *)
  Qed.
End S.
