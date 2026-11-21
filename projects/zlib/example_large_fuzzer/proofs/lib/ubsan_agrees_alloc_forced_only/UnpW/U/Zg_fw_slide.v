(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_tr_kit Z_defl_iface Z_slow_model Z_fw_model Z_fw_kit Z_ukit Z_fw_slide Zg_fw_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section SLIDE.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fwg_slide_stage : forall (X : deflate_state) (more : Z) (Q : machine_state -> Prop)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X ->
  65274 <= ds_strstart X -> more = 65536 - ds_lookahead X - ds_strstart X ->
  - 2 ^ 62 <= ds_block_start X < 2 ^ 62 ->
  (forall (mA : mem) (v1 v5 v6 v7 v10 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 : word),
     FWINV L inp lo r me (fw_slide X 32768 more) mA ->
     evt usegs Q (MS (mkR v1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) (wz (32768 + more)) v10 (wz (ds_strstart X - 32768)) v12 v13 v14 v15 v16 v17
                      (wz (dl_As L + 5932)) (wz 32768) (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) v28 v29 v30 v31)
                  F (wz Z_FW_READ) fc None mA (seg_rom usegs))) ->
  evt usegs Q (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) (wz more) y10 y11 y12 y13 y14 y15 y16 y17
                   (wz (dl_As L + 5932)) (wz 32768) (wz 3) (wz 32) y22 (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
               F (wz Z_FW_SLIDE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros INV FW SS EM RBS K. unfold Z_FW_SLIDE.
  destruct INV as (DR & DIN & (j0 & FR) & STK & MU & WM & MI). unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof FW as FW0. destruct FW as [Wws _ Wwl Wwsz Wpl _ Whs _ Whl _ _ Wins Wlook Wsl Wms _ _ _ _ _ _ _ _ _ _ Wpb Whb _].
  open_DST ST. open_A GA. open_D GD.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  (* [comment removed for export] *)
  open_win Gwin.
  pose proof (u8arr_sub_bytes _ (dl_Aw L) _ (Z.to_nat 32768) (Z.to_nat (32768 - more)) Gwin ltac:(rewrite av8_length; lia)) as SRC.
  destruct (u8arr_split3 _ (dl_Aw L) _ 0%nat (Z.to_nat (32768 - more)) Gwin ltac:(rewrite av8_length; lia)) as (_ & O2 & O3). clear Gwin LW.
  cbn [skipn] in O2. replace (dl_Aw L + Z.of_nat 0) with (dl_Aw L) in O2 by lia.
  remember (firstn (Z.to_nat (32768 - more)) (skipn (Z.to_nat 32768) (av8 (ds_window X) 65536))) as src eqn:Esrc.
  assert (Lsrc : length src = Z.to_nat (32768 - more)) by (rewrite Esrc, length_firstn, length_skipn, av8_length; lia).
  replace (Z.of_nat (Z.to_nat 32768)) with 32768 in SRC by lia.
  remember (skipn (0 + Z.to_nat (32768 - more)) (av8 (ds_window X) 65536)) as w3 eqn:Ew3.
  assert (LO3 : Z.of_nat (length w3) = 65536 - (32768 - more)) by (rewrite Ew3, length_skipn, av8_length; lia).
  replace (dl_Aw L + Z.of_nat 0 + Z.of_nat (Z.to_nat (32768 - more))) with (dl_Aw L + (32768 - more)) in O3 by lia.
  (* [comment removed for export] *)
  zs. zstep. gF. zstep. zstep. zstep. gX.
  zs. zs. zs. rewrite ?Z.mod_small by lia.
  (* [comment removed for export] *)
  zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (memcpy_Z (dl_Aw L) (dl_Aw L + 32768) (32768 - more));
                      [exact SRC| exact Lsrc| exact O2| lia| eassumption| lia| lia| lia]
                    | clear O2 SRC; post_call segs mm ] end.
  name_mem mc.
  pose proof (u8arr_join2z mc (dl_Aw L) src w3 (32768 - more) ltac:(lia) PC O3) as WIN. clear PC O3 POST LO3.
  subst src w3. replace (0 + Z.to_nat (32768 - more))%nat with (Z.to_nat (32768 - more)) in WIN by lia.
  rewrite <- (av8_blit_down (ds_window X) 65536 32768 (32768 - more)) in WIN by lia.
  pose proof (arr_len_blit (ds_window X) 0 (ds_window X) 32768 (32768 - more)) as LNW. rewrite Wwl in LNW.
  remember (arr_blit (ds_window X) 0 (ds_window X) 32768 (32768 - more)) as w' eqn:Ew'.
  pose proof (av8_zlength w' 65536 ltac:(lia)) as LWF.
  (* [comment removed for export] *)
  zs. zs. zs. zstep. zs. zs. zstep. zstep. zs. zs.
  rewrite (bs_guard (ds_block_start X)) by lia. change (Z.b2z (9223372036854775808 <? 9223372036854808576)) with 1. gF.
  zs. zs. (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (eq_refl (ins_clamp X)) as ECL. unfold ins_clamp in ECL at 1.
  destruct (Z.ltb_spec (ds_strstart X - 32768) (ds_insert X)) as [CL|CL];
    [ zstep; br_false; zs | zstep; br_true ].
  all: rename ECL into EIC.
  all: rewrite EIC in GD.
  (* [comment removed for export] *)
  all: assert (AH2 : 2 <= dl_Ah L /\ dl_Ah L mod 2 = 0) by (pose proof (lo_h _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  all: assert (AP2 : 2 <= dl_Ap L /\ dl_Ap L mod 2 = 0) by (pose proof (lo_p _ LAY) as BH; unfold blk_ok in BH; clear - BH; Z.div_mod_to_equations; lia).
  all: zs; rewrite Whs; zs; zstep; zstep; gF; zstep; zstep; zstep; gX; zstep; rewrite (land1_mod2 (dl_Ah L) (proj2 AH2)); gF; zs; rewrite Wws.
  all: replace (wz (65536 + dl_Ah L)) with (wz (dl_Ah L + 2 * 32768)) by (f_equal; lia).
  all: name_mem mA; tr_groups MUf WMf; clear MUf WMf.
  all: pose proof (munch_refl [(dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536); (dl_As L + 5881, dl_As L + 5968)] mA) as MUf; pose proof (wmono_refl usegs mA) as WMf.
  all: open_u16 Ghead; open_u16 Gprev.
  all: lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (shloop_h (Z.to_nat 32767) 32768 (ds_head X) (dl_Ah L)); [lia| lia| exact Ghead| exact Whl| exact Whb| assumption| lia| lia]
                    | clear Ghead; post_call segs mm ] end.
  all: rename POST into HEAD; remember (slide_hash_loop (Z.to_nat 32768) (ds_head X) 32768 32768) as hd eqn:Ehd.
  all: assert (LNH : arr_len hd = 32768) by (rewrite Ehd, slide_hash_loop_len; exact Whl).
  all: pose proof (av16_zlength hd 32768 ltac:(lia)) as L16h.
  all: apply box in Ehd.
  (* [comment removed for export] *)
  all: zs; zstep; zstep; gF; zstep; zstep; zstep; gX; zstep; rewrite (land1_mod2 (dl_Ap L) (proj2 AP2)); gF; zstep.
  all: replace (wz (65536 + dl_Ap L)) with (wz (dl_Ap L + 2 * 32768)) by (f_equal; lia).
  all: lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [ eapply (shloop_p (Z.to_nat 32767) 32768 (ds_prev X) (dl_Ap L)); [lia| lia| exact Gprev| exact Wpl| exact Wpb| assumption| lia| lia]
                    | clear Gprev; post_call segs mm ] end.
  all: rename POST into PREV; remember (slide_hash_loop (Z.to_nat 32768) (ds_prev X) 32768 32768) as pv eqn:Epv.
  all: assert (LNP : arr_len pv = 32768) by (rewrite Epv, slide_hash_loop_len; exact Wpl).
  all: pose proof (av16_zlength pv 32768 ltac:(lia)) as L16p.
  all: zs; zs; name_mem mF; tr_groups MUf WMf.
  all: apply K; apply unbox in Ehd.
  all: rewrite (fw_slide_eqg X more ltac:(lia) Wws Whs ltac:(lia)); rewrite <- Ehd, <- Epv.
  all: split; [split; [exact ZS|]|].
  1,3: constructor;
       [ exists hA1, hA2, hA3, hA4, hA5; unfold fw_slide4, dsA_cells; dsred; eapply rw_cells_sim; [exact GA| cells_sim_tac]; apply ms_mach
       | exact GB| exact GC
       | do 5 eexists; unfold fw_slide4, dsD_cells; dsred; close_cells GD
       | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep
       | unfold dwin, fw_slide4; dsred; rewrite <- Ew'; exact WIN
       | unfold dprev, u16arr, fw_slide4; dsred; exact PREV
       | unfold dhead, u16arr, fw_slide4; dsred; exact HEAD
       | exact Gpend
       | destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13];
         constructor; unfold fw_slide4; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9| rewrite <- Ew'; lia |exact LNP|exact LNH|exact l13]
       | exact LAY ].
  all: split; [exact (fw_din L inp nout lo r me CTX mF MU)|]; split; [eexists; exact FR|]; split; [exact STK|]; split; [exact MU|]; split; [exact WM| assumption].
Qed.
End SLIDE.
