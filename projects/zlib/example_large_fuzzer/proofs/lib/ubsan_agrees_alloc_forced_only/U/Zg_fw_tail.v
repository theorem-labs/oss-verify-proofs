(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_fw_model Z_fw_kit Z_fw_high Z_ukit Zg_fw_model Zg_fw_insert.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel LmatchModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Section TAIL.
Variables (L : dlay) (inp : list Z) (nout lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : fw_ctx L inp nout lo r me.

Lemma fwg_tail : forall (X : deflate_state) (n : Z)
    (y1 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y19 y23 y28 y29 y30 y31 : word) (m : mem),
  FWINV L inp lo r me X m -> fw_wf 32768 32768 X ->
  0 <= n -> ds_strstart X + ds_lookahead X + n <= 65536 ->
  (ds_lookahead X + n <= 261 -> cs_avail_in (ds_strm X) = 0) ->
  evt usegs (fw_post_gen r F fc L (fill_window_high (fw_insert (set_lookahead X (ds_lookahead X + n)))) inp lo me)
    (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) y5 y6 y7 (wz (dl_As L)) y9 (wz n) y11 y12 y13 y14 y15 y16 y17
             (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) (wz 2) (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) y28 y29 y30 y31)
        F (wz Z_FW_TAIL) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros (DR & DIN & (j0 & FR) & STK & MU & WM & MI) FW Hn SLN EXIT. unfold Z_FW_TAIL. unfold fw_W in MU. unfold fw_frame in FR.
  pose proof CTX as CTX'. destruct CTX' as [LOsp SP16 LAY0 BEL IO DIN0]. unfold Z_FILLWIN_STACK in LOsp.
  pose proof (bv_unsigned_in_range 64 (r_sp r)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct DR as [ZS ST]. pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
  pose proof (lo_S _ LAY) as BKS.
  pose proof FW as FW0. destruct FW as [Wws Wwsr Wwl Wwsz Wpl Wwm Whs Whsr Whl Whm Whsh Wins Wlook Wsl Wms Wih Whw Wni Wai Winl Wti Wwr Wad1 Wad2 Wwb Wpb Whb Wib].
  open_DST ST. open_A GA. open_D GD. open_win Gwin. open_u16 Gprev. open_u16 Ghead.
  pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ap L, dl_Ap L + 65536); (dl_Ah L, dl_Ah L + 65536)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  pose proof (munch_refl [(dl_As L, dl_As L + 212)] m) as MUf1. pose proof (wmono_refl usegs m) as WMf1.
  (* [comment removed for export] *)
  assert (KEND : forall (X3 : deflate_state) (mA : mem) (j0 : list byte) (v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 v29 : word),
    dzs mA L (ds_strm X) -> DST mA L X3 -> ds_strm X3 = ds_strm X -> fw_wf 32768 32768 X3 ->
    rw_cells usegs mA (bv_unsigned (r_sp r) + -96) (fw_frame j0 r) -> stk usegs mA lo (bv_unsigned (r_sp r) + -96) ->
    munch [(lo, bv_unsigned (r_sp r)); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Aw L, dl_Aw L + 65536);
           (dl_Ap L, dl_Ap L + 2 * 32768); (dl_Ah L, dl_Ah L + 2 * 32768)] me mA -> wmono usegs me mA -> mem_inv usegs mA ->
    evt usegs (fw_post_gen r F fc L (fill_window_high X3) inp lo me)
      (MS (mkR y1 (wz (bv_unsigned (r_sp r) + -96)) (r_gp r) (r_tp r) v5 v6 v7 (wz (dl_As L)) y9 (wz (ds_lookahead X + n)) v11 v12 v13 v14 v15 v16 v17
               (wz (dl_As L + 5932)) y19 (wz 3) (wz 32) (wz 2) (wz 261) y23 (wz 1) (r_s10 r) (r_s11 r) v28 v29 y30 y31)
          F (wz 0x16d50) fc None mA (seg_rom usegs))).
  { intros X3 mA jK v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 v29 ZSA STA ES3 FW3 FRA STKA MUA WMA MIA.
    destruct STA as [A3 B3 C3 D3 lt3 dt3 bt3 blc3 heap3 dep3 win3 prev3 head3 pend3 LENS3 LAY3].
    destruct A3 as (g1 & g2 & g3 & g4 & g5 & A3). unfold dsA_cells in A3. destruct ZSA as (q1 & q2 & q3 & q4 & ZSA). unfold zs_call_cells, zs_priv_cells in ZSA. cbn [app] in ZSA.
    unfold fw_frame in FRA.
    zstep. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
    - apply (fw_high L inp nout lo r F fc me CTX X3). 2:{ exact FW3. }
      split; [split; [exists q1, q2, q3, q4; rewrite ES3; exact ZSA| ]|].
      + constructor; [exists g1, g2, g3, g4, g5; exact A3| exact B3| exact C3| exact D3| exact lt3| exact dt3| exact bt3| exact blc3| exact heap3| exact dep3
                     | exact win3| exact prev3| exact head3| exact pend3| exact LENS3| exact LAY3].
      + split; [exact (fw_din L inp nout lo r me CTX mA MUA)|]. split; [eexists; exact FRA|]. split; [exact STKA|]. split; [exact MUA|]. split; [exact WMA| exact MIA].
    - zs. gF. zstep. al8 (dl_S L). gF. zs. rewrite (EXIT ltac:(lia)). zstep. if_false.
      apply (fw_high L inp nout lo r F fc me CTX X3). 2:{ exact FW3. }
      split; [split; [exists q1, q2, q3, q4; rewrite ES3; exact ZSA| ]|].
      + constructor; [exists g1, g2, g3, g4, g5; exact A3| exact B3| exact C3| exact D3| exact lt3| exact dt3| exact bt3| exact blc3| exact heap3| exact dep3
                     | exact win3| exact prev3| exact head3| exact pend3| exact LENS3| exact LAY3].
      + split; [exact (fw_din L inp nout lo r me CTX mA MUA)|]. split; [eexists; exact FRA|]. split; [exact STKA|]. split; [exact MUA|]. split; [exact WMA| exact MIA]. }
  zs. zs. zs. zs. zs. (* [comment removed for export] *)
  zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
  - (* [comment removed for export] *)
    replace (fw_insert (set_lookahead X (ds_lookahead X + n))) with (set_lookahead X (ds_lookahead X + n))
      by (unfold fw_insert; dsred; replace (MIN_MATCH <=? ds_lookahead X + n + ds_insert X) with false by (symmetry; apply Z.leb_gt; unfold MIN_MATCH; lia); reflexivity).
    name_mem mA. clear MUf WMf. tr_groups MUf1 WMf1.
    eapply KEND; [exact ZS| | reflexivity| | exact FR| exact STK| exact MU| exact WM| assumption].
    + constructor; [do 5 eexists; unfold dsA_cells; dsred; close_cells GA| exact GB| exact GC| do 5 eexists; unfold dsD_cells; dsred; close_cells GD
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| exact Gwin
                   | unfold dprev, u16arr; dsred; exact Gprev| unfold dhead, u16arr; dsred; exact Ghead| exact Gpend| close_lens LENS| exact LAY].
    + destruct FW0; constructor; dsred; first [assumption | lia].
  - (* [comment removed for export] *)
    clear MUf1 WMf1.
    zs. zs. zs.
    remember (ds_strstart X - ds_insert X) as str eqn:Estr.
    zstep. zstep. rewrite ?Z.mod_small by lia. zstep. gF. zstep. zstep. zstep. gX. gF.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) str ltac:(apply Wwb; lia).
    zs. zs. (* [comment removed for export] *)
    gF.
    zstep. zstep. zstep. rewrite ?Z.mod_small by lia. zstep. rewrite zb_lxor_ones by lia. gF.
    zs.
    ld8 Gwin (ds_window X) 65536 (dl_Aw L) (str + 1) ltac:(apply Wwb; lia).
    zs. zs. zs. zs.
    rewrite (Z.mod_small (arr_get (ds_window X) str) 18446744073709551616) by (pose proof (Wwb str ltac:(lia)); lia).
    rewrite (hash_mach X (arr_get (ds_window X) str) (arr_get (ds_window X) (str + 1))) by lia.
    pose proof (update_hash_range X (arr_get (ds_window X) str) (arr_get (ds_window X) (str + 1)) ltac:(lia)) as Rhv.
    remember (update_hash X (arr_get (ds_window X) str) (arr_get (ds_window X) (str + 1))) as h eqn:Eh.
    zs. (* [comment removed for export] *)
    name_mem m1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (fw_insloop L r F fc hA1 hA2 hA3 hA4 hA5 hD0 hD1 hD2 hD3 hD4 _ _ _ _ _ _ _ _ _ _ _ _ LAY (Z.to_nat (ds_insert X))
                                 (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h) str)
                      | clear GA GD Gprev Ghead; post_call segs mm ] end.
    + dsred. lia.
    + subst h. destruct FW0; constructor; dsred; first [assumption | lia | apply update_hash_range; lia].
    + lia.
    + dsred. lia.
    + dsred. lia.
    + unfold dsA_cells. dsred. close_cells GA.
    + unfold dsD_cells. dsred. close_cells GD.
    + dsred. exact Gwin.
    + dsred. exact Gprev.
    + dsred. exact Ghead.
    + assumption.
    + name_mem m2. rename PC into GA2. rename PC0 into GD2. rename PC1 into P2. rename POST into H2.
      change (ds_insert (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h)) with (ds_insert X) in *.
      change (ds_lookahead (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h)) with (ds_lookahead X + n) in *.
      assert (FW2 : fw_wf 32768 32768 (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h)).
      { subst h. destruct FW0; constructor; dsred; first [assumption | lia | apply update_hash_range; lia]. }
      destruct (fill_window_insert_wf (Z.to_nat (ds_insert X)) 32768 32768 (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h) str
                  ltac:(dsred; lia) FW2 ltac:(lia) ltac:(dsred; lia) ltac:(dsred; lia)) as (FW3 & FC3 & L3 & S3 & A3).
      change (ds_insert (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h)) with (ds_insert X) in FW3.
      replace (fw_insert (set_lookahead X (ds_lookahead X + n)))
        with (fill_window_insert (Z.to_nat (ds_insert X)) (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h) str).
      2:{ unfold fw_insert. dsred. replace (MIN_MATCH <=? ds_lookahead X + n + ds_insert X) with true by (symmetry; apply Z.leb_le; unfold MIN_MATCH; lia).
          subst str h. reflexivity. }
      destruct (fill_window_insert_shape (Z.to_nat (ds_insert X)) (set_ins_h (set_ins_h (set_lookahead X (ds_lookahead X + n)) (arr_get (ds_window X) str)) h) str)
        as (pv & hd & ih & ins & ES & Lp & Lh).
      rewrite ES in GA2, GD2, P2, H2, FW3 |- *.
      tr_groups MUf WMf.
      eapply KEND; [exact ZS| | reflexivity| exact FW3| exact FR| exact STK| exact MU| exact WM| assumption].
      constructor; [exists hA1, hA2, hA3, hA4, hA5; exact GA2| exact GB| exact GC| exists hD0, hD1, hD2, hD3, hD4; exact GD2
                   | exact Glt| exact Gdt| exact Gbt| exact Gblc| exact Gheap| exact Gdep| unfold dwin; dsred; exact Gwin
                   | unfold dprev, u16arr; dsred; exact P2| unfold dhead, u16arr; dsred; exact H2| exact Gpend| | exact LAY].
      revert Lp Lh. dsred. intros Lp Lh.
      destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
      constructor; dsred; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10| rewrite Lp; exact l11| rewrite Lh; exact l12|exact l13].
Qed.
End TAIL.
