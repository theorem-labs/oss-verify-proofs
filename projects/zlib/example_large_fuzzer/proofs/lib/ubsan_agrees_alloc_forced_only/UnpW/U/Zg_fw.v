(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_slow_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_defl_iface Z_slow_model Z_fw_model Z_fw_kit Z_fw_high Z_ukit Zg_adler32_iface Zg_readbuf Zg_defl_iface Zg_fw_model Zg_fw_insert Zg_fw_tail Zg_fw_read Zg_fw_slide.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Theorem fill_window_specg : adler32_stmt -> fill_window_stmtg.
Proof.
  intros HADL. unfold fill_window_stmtg. intros until m. intros DR DIN TIE MI STK LOG SP16 BEL IO FW W2 AI RBS ->. unfold Z_FILL_WINDOW.
  assert (LO : lo <= bv_unsigned sp - Z_FILLWIN_STACK) by (unfold Z_FILLWIN_STACKG in LOG; exact LOG).
  set (r := mkSR ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  enough (G : evt usegs (fw_post_gen r F fc L (fill_window d) inp lo m)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (dl_As L)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x16a08) fc None m (seg_rom usegs))) by exact G.
  pose proof (st_lay _ _ _ _ (proj2 DR)) as LAY.
  assert (CTX : fw_ctx L inp nout lo r m) by (constructor; assumption).
  rewrite (fill_window_eqg d FW).
  pose proof (fwA_factsg d FW) as FA. pose proof (proj1 (fw_more_eqg d FW)) as EMQ.
  lay_open LAY. pose proof BEL as BEL0. below_open BEL0. pose proof IO as I0. io_open I0. unfold Z_FILLWIN_STACK in LO.
  pose proof (lo_s _ LAY) as BKs. unfold blk_ok in BKs.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof FW as FW0. destruct FW as [Wws _ Wwl Wwsz _ _ Whs _ _ _ _ Wins Wlook Wsl _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  pose proof DR as DR0. destruct DR0 as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA.
  pose proof (munch_refl (fw_W L lo r) m) as MU. unfold fw_W in MU. cbn [r_sp r] in MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf. pose proof (wmono_refl usegs m) as WMf.
  (* [comment removed for export] *)
  carve_frame 96%nat STK.
  do 12 zs.
  zs. zstep. al8 (dl_As L). gF.
  zs. zs. rewrite Wws. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  (* [comment removed for export] *)
  zs. zs. rewrite Wws. zs. zs. zs. rewrite ?Z.mod_small by lia. zs. zs. zs.
  name_mem mH. clear GA.
  assert (INV : FWINV L inp lo r m d mH).
  { split.
    { apply (DREP_agree m mH L d DR).
      - eapply ag_blocks_munch; [exact LAY| exact MUf| exact WMf| | | | |]; cbn [disjoint_from]; slia.
      - apply (agree_on_of_munch [(lo, bv_unsigned sp)]); [exact MUf| exact WMf| lia| lia| cbn [disjoint_from]; slia]. }
    split; [exact (fw_din L inp nout lo r m CTX mH MU)|]. split; [eexists; exact FR|]. split; [exact STK|]. split; [exact MU|]. split; [exact WM| assumption]. }
  clear MUf WMf FR STK MU WM.
  replace (wz (ds_window_size d - (ds_lookahead d + ds_strstart d))) with (wz (fw_more0 d)) by (unfold fw_more0; f_equal; lia).
  zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia.
  - (* [comment removed for export] *)
    unfold fwA, moreA, slide_cond. replace (65274 <=? ds_strstart d) with false by (symmetry; apply Z.leb_gt; lia).
    unfold fwA, moreA, slide_cond in FA. replace (65274 <=? ds_strstart d) with false in FA by (symmetry; apply Z.leb_gt; lia).
    destruct FA as (_ & _ & _ & _ & _ & _ & ZL0 & FULL0).
    apply (fwg_read L inp nout lo r F fc m CTX HADL d (fw_more0 d)); [exact INV| exact FW0| exact W2| exact AI| exact TIE| unfold fw_more0; lia| exact ZL0| exact FULL0].
  - (* [comment removed for export] *)
    unfold fwA, moreA, slide_cond in FA |- *. replace (65274 <=? ds_strstart d) with true in FA |- * by (symmetry; apply Z.leb_le; lia).
    rewrite EMQ in FA |- *. destruct FA as (FW1 & WR1 & ZS1 & _ & EM1 & _ & ZL1 & FULL1).
    destruct (fw_slide_wf 32768 32768 d (fw_more0 d) FW0 ltac:(lia) ltac:(unfold fw_more0; lia)) as (_ & _ & _ & ES1).
    eapply (fwg_slide_stage L inp nout lo r F fc m CTX d (fw_more0 d)); [exact INV| exact FW0| lia| unfold fw_more0; lia| exact RBS|].
    intros mA v1 v5 v6 v7 v10 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 INV1.
    replace (wz (32768 + fw_more0 d)) with (wz (fw_more0 d + 32768)) by (f_equal; lia).
    replace (wz (ds_strstart d - 32768)) with (wz (ds_strstart (fw_slide d 32768 (fw_more0 d)))) by (f_equal; exact ES1).
    apply (fwg_read L inp nout lo r F fc m CTX HADL (fw_slide d 32768 (fw_more0 d)) (fw_more0 d + 32768));
      [exact INV1| exact FW1| rewrite WR1; exact W2| rewrite ZS1; exact AI| unfold din_tie; rewrite ZS1; exact TIE| exact EM1| exact ZL1| exact FULL1].
Qed.
