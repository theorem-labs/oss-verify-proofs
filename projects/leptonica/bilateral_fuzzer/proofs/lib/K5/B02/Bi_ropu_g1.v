(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit Cf_iface Cf_kit Km_setelem Km_iface Km_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_ropkit Bi_ropu_iface Bi_ropu_kit LeptB_guard LeptB_guard2 LeptB_guard3.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The first-word and last-word masks: the bytes of lmask32 (0x28da0) and rmask32 (0x28ce0), read from the image. *)
Local Lemma ropu_lmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x28da0 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x28da0 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x28da0 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (image_bytes_length asegs _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.
Local Lemma ropu_rmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x28ce0 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x28ce0 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x28ce0 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (image_bytes_length asegs _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.
Local Lemma ropu_ztobv_modM : forall e, Z_to_bv 64 (e mod 18446744073709551616) = Z_to_bv 64 e.
Proof. intros e. exact (ZBridge.Z_to_bv_mod64 e). Qed.
Local Lemma ropu_swrap32_modadd : forall A B, - 2^31 <= A + B < 2^31 -> bv_swrap 32 (A mod 18446744073709551616 + B) = A + B.
Proof.
  intros A B H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  change (2^31) with 2147483648 in H.
  Z.div_mod_to_equations. lia.
Qed.
Local Lemma ropu_srliw5_small : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32.
Proof.
  intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia].
Qed.
(* A row of the destination: the bytes the loop touches in row dy + i' lie inside the dpixh rows of dwpl words. *)
Local Ltac ropu_rowfit dwpl dpixh dy :=
  let i' := fresh "i'" in let Hi := fresh "Hi'" in intros i' Hi;
  let M := fresh "M" in let N := fresh "N" in
  assert (M : dwpl * (dy + i' + 1) <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia);
  assert (N : 0 <= dwpl * (dy + i')) by (apply Z.mul_nonneg_nonneg; lia);
  split; lia.

(* The walk's normalisation between steps (B: the hidden bounds of the walk). *)
Local Ltac ropu_cnb B :=
  rewrite ?Z.add_0_r;
  repeat match goal with |- context [bv_swrap 32 (bv_wrap 32 ?j / ?d) mod 18446744073709551616] =>
    rewrite (srliw_idx j d) by (clear - B; unfold hid in *; lia) end;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - B; unfold hid in *; lia) end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - B; unfold hid in *; lia) end;
  rewrite ?ropu_ztobv_modM.
Local Ltac ropu_bwalk stops B := repeat (tryif at_stop stops then fail else (ropu_cnb B; awalk1)).
Local Ltac ropu_dedup_ro := repeat match goal with H1 : ro_cells asegs ?m ?a ?c, H2 : ro_cells asegs ?m ?a ?c |- _ => clear H2 end.
Local Ltac ropu_drop_acc a := repeat match goal with H : acc asegs _ a _ |- _ => clear H end.

Section ROPUG1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (167136, 132) ACC_LITS.
Hypothesis TABL : In (167328, 132) ACC_LITS.

Lemma ropu_clr_g1 : rasteropUniLow_clr_case RT 1.
Proof using AF GP FKC TABR TABL.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad dpixw dpixh dwpl dx dy dw dh FDO MST -> -> -> -> -> -> -> -> ARGS DX0 DY0 DW0 DH0 DXW DYH DPW DPH
    DWPL DWC DNHI CH ENV RES DXMOD.
  unfold lpost, lenv, keeps, keepsL, chunk, PIX_CLR in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct CH as (DIN & D0 & D16 & DSZ).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_rasteropUniLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + 4 * (dwpl * dpixh))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP datad (4 * (dwpl * dpixh)).
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABL) as ACCL. cbn [fst snd] in ACCL.
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABR) as ACCR. cbn [fst snd] in ACCR.
  refresh RT AF; unfold shad, SHB in *; park_disj.
  assert (BD : 0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh /\ dpixw <= 20000 /\ dpixh <= 20000) by lia.
  hide BD.
  ropu_dedup_ro. ropu_drop_acc datad.
  unfold hid in BD.
  walk_to AF MST [(usp - 64, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xb3b1c].
  rewrite ?Z.add_0_r.
  lstep;
    change 31 with (Z.ones 5); rewrite (Z.land_ones (dx * 8) 5) by lia; change (2^5) with 32.
  set (xb := (dx * 8) mod 32) in *.
  assert (XBR : 0 <= xb < 32) by (unfold xb; apply Z.mod_pos_bound; lia).
  assert (XBV : xb = 8) by (unfold xb; change 32 with (4 * 8); rewrite Z.mul_mod_distr_r by lia; rewrite DXMOD; reflexivity).
  lstep.
  brfork XB0.
  { exfalso. clear - XB0 XBV. lia. }
  assert (XBN : 1 <= xb <= 31) by (clear - XBR XB0; lia).
  assert (WPLB : 0 < dwpl <= 16777216).
  { assert (dwpl * 1 <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (BD2 : 0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 16777216).
  { clear - BD WPLB DNHI.
    pose proof (Z.mul_nonneg_nonneg dy dwpl ltac:(lia) ltac:(lia)) as N1.
    pose proof (Z.mul_le_mono_nonneg_r (dy + dh) dpixh dwpl ltac:(lia) ltac:(lia)) as N3.
    rewrite Z.mul_add_distr_r in N3. rewrite (Z.mul_comm dpixh dwpl) in N3. lia. }
  assert (FWD : 0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) by (clear - BD; split; split; try (apply Z.div_pos; lia); apply Z.div_le_upper_bound; lia).
  assert (DHI : datad + 4 * (dwpl * dpixh) <= 140737488355328) by lia.
  assert (NB : (0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh /\ dpixw <= 20000 /\ dpixh <= 20000)
            /\ (0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 16777216) /\ 0 < dwpl <= 16777216
            /\ (0 <= dx * 8 / 32 <= 5000 /\ 0 <= dw * 8 / 32 <= 5000) /\ 0 < datad /\ datad + 4 * (dwpl * dpixh) <= 140737488355328 /\ 1 <= xb <= 31).
  { repeat split; try (clear - BD; lia); try (clear - BD2; lia); try (clear - WPLB; lia); try (clear - FWD; lia); try (clear - XBN; lia); try assumption; lia. }
  hide NB.
  ropu_bwalk [0xb3ba8] NB.
  lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
    destruct (ropu_rmask_bytes mm MIx) as (rbs & RB & RBL);
    destruct (bytes_at_read4w mm 0x28ce0 rbs ((32 - xb) * 4) RB ltac:(clear - XBN; lia) ltac:(rewrite RBL; clear - XBN; lia)) as (fm & RM) end;
    lstep; clear RM RB RBL rbs.
  ropu_bwalk [0xb3bb0] NB.
  ropu_cnb NB.
  (* The epilogue from 0xb42bc: the frame reloads, the return, and the post-condition. *)
  lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mcur _) =>
    assert (EPI : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word) (mE : mem),
      munch [(datad, datad + 4 * (dwpl * dpixh))] mcur mE -> wmono asegs mcur mE -> mem_inv asegs mE ->
      evt asegs (fun ms' => cps asegs (ASTA RT Σ PMc (eq ms')) QF)
        (MS (mkR ra' (Z_to_bv 64 (usp + -64)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F0 (Z_to_bv 64 0xb42bc) fc0 None mE (seg_rom asegs))) end.
  { intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' mE MUE WME MIE.
    loop_art RT AF Σ mE lo MUE
      ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dpixh)); split; [solve [in_live_tac]| lia]| exact I]]).
    lazymatch type of MUE with munch _ ?mm ?me =>
      loop_transport mm me MUE ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
    clear MUE WME.
    cwalk (@nil Z); cps_stop.
    agf_munch AGF MU ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; destruct Hx as [_ HxO]; cbn [outside] in HxO;
                                     clear - P HxO LOR; split; [lia| split; [tauto| exact I]]).
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-.
    do 2 eexists; split; [split; [unfold ret_st; do 16 eexists; reflexivity| apply fs_agree_refl]|].
    split; [split; [split; [exact ARTl| split; [exact MIE| split; [| assumption]]]| split; assumption]|];
      [ repeat match goal with H : wmono asegs _ _ |- _ => revert H end; clear; intros; eauto using wmono_trans
      | intros a Ha Ho; exact (AGF a (conj Ha Ho)) ]. }
  pose (dnf := (dw * 8 - (32 - xb)) / 32). pose (dlw := (dw * 8 + dx * 8) mod 32). pose (fw := dx * 8 / 32).
  assert (GF1 : fw + 1 <= dwpl) by (clear - BD DWC; unfold fw; Z.div_mod_to_equations; lia).
  assert (GF2 : 32 - xb <= dw * 8 -> fw + 1 + dnf <= dwpl) by (clear - BD DWC XBN; unfold fw, dnf, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (GF2b : 32 - xb <= dw * 8 -> 0 <= dnf <= 5000) by (clear - BD XBN; unfold dnf, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (GF3 : 32 - xb <= dw * 8 -> dlw <> 0 -> fw + 1 + dnf + 1 <= dwpl) by (clear - BD DWC XBN; unfold fw, dnf, dlw, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (DLWR : 0 <= dlw < 32) by (unfold dlw; apply Z.mod_pos_bound; lia).
  lazymatch goal with MUx : munch ?W ?m0 ?mm, WMx : wmono asegs ?m0 ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (ARTn : ART RT Σ mm)
      by (apply (art_client_writes RT AF Σ m0 mm lo W ART0 MUx WMx); [unfold STACK_WIN; lia|
          cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists datad, (4 * (dwpl * dpixh)); split; [exact DIN| lia]| exact I]]]);
    pose proof (af_acc_live RT AF Σ mm datad (4 * (dwpl * dpixh)) ARTn DIN) as (WRD & ACCD) end.
  assert (D4 : datad mod 4 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
  assert (OUTD : datad + 4 * (dwpl * dpixh) <= 0x7fff8000 \/ 0x10007fff8000 <= datad) by (unfold parked in *; lia).
  lstep.
  (* Up to the first-word rows at 0xb3e14: the masks, the full-word count, the last-word flag. *)
  lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
    eapply (evt_cut asegs (fun ms' => exists (v_t0 v_s0 v_a2 v_a5 v_a6 v_a7 v_t4 v_t5 : word),
      ms' = MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp v_t0 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v_s0 s1
                    (Z_to_bv 64 (dx * 8 / 32 * 4 + (dwpl * dy * 4 + datad))) (Z_to_bv 64 (dwpl * 4)) v_a2 (Z_to_bv 64 dh) (Z_to_bv 64 0) v_a5 v_a6 v_a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (dx * 8 / 32 * 4 + (dwpl * dy * 4 + datad))) v_t4 v_t5 (Z_to_bv 64 dh))
               F0 (Z_to_bv 64 0xb3e14) fc0 None mm (seg_rom asegs)
      /\ (v_t5 = Z_to_bv 64 1 \/ (v_t5 = Z_to_bv 64 0 /\ v_a6 = Z_to_bv 64 dnf /\ v_a7 = Z_to_bv 64 (dx * 8 / 32 * 4 + (dwpl * dy * 4 + datad) + 4) /\ 32 <= dw * 8 - (32 - xb)))
      /\ (v_t0 = Z_to_bv 64 1 \/ (v_t0 = Z_to_bv 64 0 /\ v_a2 = Z_to_bv 64 (dx * 8 / 32 * 4 + (dwpl * dy * 4 + datad) + 4 + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
  {
    destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
    { (* The first word is the only word of each row. *)
      brF.
      lstep.
      rewrite (ropu_swrap32_modadd (dw * 8 - (32 - xb)) 32) by (clear - NB DP; unfold hid in *; lia).
      ropu_bwalk [0xb3bf0] NB.
      ropu_cnb NB.
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
        reg_val (Z_to_bv 5 10) ltac:(fun v => lazymatch v with Z_to_bv 64 (167328 + ?kk) =>
          destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
          destruct (bytes_at_read4w mm 0x28da0 rbs kk RB ltac:(clear - NB DP; unfold hid in *; lia) ltac:(rewrite RBL; clear - NB DP; unfold hid in *; lia)) as (lm & RM) end) end;
        lstep; clear RM RB RBL rbs.
      ropu_bwalk [0xb3ddc] NB.
      ropu_cnb NB.
      replace (Z.b2z (dw * 8 <? 32 - xb)) with 1 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [reflexivity| lia]);
        lazymatch goal with |- context [Z.lor 1 (Z.b2z ?c)] => replace (Z.lor 1 (Z.b2z c)) with 1 by (destruct c; reflexivity) end.
      lstep. brF.
      ropu_bwalk [0xb3e14] NB.
      ropu_cnb NB.
      rewrite ?(slt0_nonneg dwpl) by (clear - WPLB; lia). cbn [Z.b2z].
      apply evt_done; do 8 eexists; split; [reflexivity|]; split; [left; reflexivity| left; reflexivity].
    }
    brT.
    ropu_bwalk [0xb3c38] NB.
    ropu_cnb NB.
    rewrite !(ropu_srliw5_small (dw * 8 - (32 - xb))) by (clear - NB NDP; unfold hid in *; lia).
    fold dnf.
    lstep.
    destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL].
    { (* No full word: the first word and, when dlw <> 0, a last word. *)
      assert (DNF0 : dnf = 0) by (unfold dnf; apply Z.div_small; lia).
      brT.
      ropu_bwalk [0xb3ddc] NB.
      ropu_cnb NB.
      replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
      replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
      destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
      { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
        change (Z.lor 0 1) with 1.
        lstep. brF.
        ropu_bwalk [0xb3e14] NB.
        ropu_cnb NB.
        rewrite ?(slt0_nonneg dwpl) by (clear - WPLB; lia). cbn [Z.b2z].
        apply evt_done; do 8 eexists; split; [reflexivity|]; split; [left; reflexivity| left; reflexivity].
      }
      replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
      change (Z.lor 0 0) with 0.
      lstep. brT.
      ropu_bwalk [0xb3eb0] NB.
      ropu_cnb NB.
      lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
        destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
        destruct (bytes_at_read4w mm 0x28da0 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end;
        lstep; clear RM RB RBL rbs.
      ropu_bwalk [0xb3e14] NB.
      ropu_cnb NB.
      rewrite ?(slt0_nonneg dwpl) by (clear - WPLB; lia). cbn [Z.b2z].
      apply evt_done; do 8 eexists; split; [reflexivity|]; split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
    }
    assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
    brF.
    ropu_bwalk [0xb3ddc] NB.
    ropu_cnb NB.
    replace (Z.land (dx * 8 + dw * 8) 31) with dlw by (unfold dlw; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; f_equal; lia).
    replace (Z.b2z (dw * 8 <? 32 - xb)) with 0 by (symmetry; destruct (Z.ltb_spec (dw * 8) (32 - xb)); [lia| reflexivity]).
    destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
    { replace (Z.b2z (dlw <? 1)) with 1 by (symmetry; destruct (Z.ltb_spec dlw 1); [reflexivity| lia]).
      change (Z.lor 0 1) with 1.
      lstep. brF.
      ropu_bwalk [0xb3e14] NB.
      ropu_cnb NB.
      rewrite ?(slt0_nonneg dwpl) by (clear - WPLB; lia). cbn [Z.b2z].
      apply evt_done; do 8 eexists; split; [reflexivity|]; split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
    }
    replace (Z.b2z (dlw <? 1)) with 0 by (symmetry; destruct (Z.ltb_spec dlw 1); [lia| reflexivity]).
    change (Z.lor 0 0) with 0.
    lstep. brT.
    ropu_bwalk [0xb3eb0] NB.
    ropu_cnb NB.
    lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
      destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
      destruct (bytes_at_read4w mm 0x28da0 rbs (dlw * 4) RB ltac:(clear - DLWR; lia) ltac:(rewrite RBL; clear - DLWR; lia)) as (lm & RM) end;
      lstep; clear RM RB RBL rbs.
    ropu_bwalk [0xb3e14] NB.
    ropu_cnb NB.
    rewrite ?(slt0_nonneg dwpl) by (clear - WPLB; lia). cbn [Z.b2z].
    apply evt_done; do 8 eexists; split; [reflexivity|]; split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
  }
  intros ms' (v_t0 & v_s0 & v_a2 & v_a5 & v_a6 & v_a7 & v_t4 & v_t5 & -> & GC & GL).
  (* The first-word rows. *)
  eapply evt_cut.
  { eapply (ugf_rows0 (Z.to_nat dh)) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (dwpl := dwpl) (dh := dh);
      first [ exact WRD | exact ACCD | assumption
            | rewrite Z2Nat.id by lia; reflexivity
            | lia
            | exact CKH
            | clear - D16 FWD WPLB BD2 DY0 DWPL; Z.div_mod_to_equations; lia
            | unfold fw in GF1; ropu_rowfit dwpl dpixh dy ]. }
  intros ms' PO1. unfold ugf_exit in PO1.
  destruct PO1 as (x1 & x2 & x3 & x4 & x5 & mA & -> & MU1 & WM1 & MI1).
  pose proof (wr_at_transport asegs _ _ datad (4 * (dwpl * dpixh)) WRD WM1) as WRDA.
  pose proof (Bi_ropkit.acc_munch_out _ _ _ _ datad (4 * (dwpl * dpixh)) MU1 OUTD ltac:(lia) ltac:(lia) ACCD) as ACCA.
  lstep.
  destruct GC as [V5|(V5 & V6 & V7 & FULL)].
  { (* No full words. *)
    subst v_t5. brT.
    lstep.
    destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
    { subst v_t0. brF.
      ropu_bwalk [0xb42bc] NB.
      eapply EPI; [exact MU1| exact WM1| exact MI1]. }
    subst v_t0 v_a2.
    first [brT | brF].
    ropu_bwalk [0xb44fc] NB.
    ropu_cnb NB.
    eapply evt_cut.
    { eapply (ugl_rows0 (Z.to_nat dh)) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (dwpl := dwpl) (dh := dh);
        first [ exact WRDA | exact ACCA | assumption
              | rewrite Z2Nat.id by lia; reflexivity
              | lia
              | exact CKH
              | clear - D16 FWD WPLB BD2 DY0 DWPL; Z.div_mod_to_equations; lia
              | pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
                unfold fw, dnf in *; ropu_rowfit dwpl dpixh dy ]. }
    intros ms' PO3. unfold ugl_exit in PO3.
    destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & -> & MU3 & WM3 & MI3).
    eapply EPI; [exact (munch_trans _ _ _ _ MU1 MU3)| exact (wmono_trans asegs _ _ _ WM1 WM3)| exact MI3].
  }
  (* The full-word rows, then the last word. *)
  subst v_t5 v_a6 v_a7. brF.
  assert (NDP : 32 - xb <= dw * 8) by (clear - FULL; lia).
  assert (DNF1 : 1 <= dnf <= 5000) by (pose proof (GF2b NDP); unfold dnf in *; split; [apply Z.div_le_lower_bound; lia| lia]).
  ropu_bwalk [0xb4224] NB.
  ropu_cnb NB.
  replace (Z.land (dx * 8 / 32 * 4 + (dwpl * dy * 4 + datad) + 4) 3) with 0
    by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - D16; Z.div_mod_to_equations; lia).
  change (Z.b2z (0 <? 1)) with 1. cbn [Z.b2z Z.ltb Z.eqb Z.compare].
  eapply evt_cut.
  { eapply (ugw_rows0 (Z.to_nat dh)) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (dwpl := dwpl) (dh := dh) (n := dnf);
      first [ exact WRDA | exact ACCA | assumption
            | rewrite Z2Nat.id by lia; reflexivity
            | lia
            | exact CKH
            | clear - D16 FWD WPLB BD2 DY0 DWPL; Z.div_mod_to_equations; lia
            | pose proof (GF2 NDP) as GF2'; unfold fw, dnf in *; ropu_rowfit dwpl dpixh dy ]. }
  intros ms' PO2. unfold ugw_rows_exit in PO2.
  destruct PO2 as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & mB & -> & MU2 & WM2 & MI2).
  pose proof (munch_trans _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
  pose proof (wr_at_transport asegs _ _ datad (4 * (dwpl * dpixh)) WRDA WM2) as WRDB.
  pose proof (Bi_ropkit.acc_munch_out _ _ _ _ datad (4 * (dwpl * dpixh)) MU2 OUTD ltac:(lia) ltac:(lia) ACCA) as ACCB.
  lstep.
  destruct GL as [V0|(V0 & V2 & DLWN & NDPL)].
  { subst v_t0. brF.
    ropu_bwalk [0xb42bc] NB.
    eapply EPI; [exact MU12| exact WM12| exact MI2]. }
  subst v_t0 v_a2.
  first [brT | brF].
  ropu_bwalk [0xb44fc] NB.
  ropu_cnb NB.
  eapply evt_cut.
  { eapply (ugl_rows0 (Z.to_nat dh)) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (dwpl := dwpl) (dh := dh);
      first [ exact WRDB | exact ACCB | assumption
            | rewrite Z2Nat.id by lia; reflexivity
            | lia
            | exact CKH
            | clear - D16 FWD WPLB BD2 DY0 DWPL; Z.div_mod_to_equations; lia
            | pose proof (GF2 NDPL) as GF2'; pose proof (GF3 NDPL DLWN) as GF3'; pose proof (GF2b NDPL) as GF2b';
              unfold fw, dnf in *; ropu_rowfit dwpl dpixh dy ]. }
  intros ms' PO3. unfold ugl_exit in PO3.
  destruct PO3 as (z1 & z2 & z3 & z4 & z5 & mC & -> & MU3 & WM3 & MI3).
  eapply EPI; [exact (munch_trans _ _ _ _ MU12 MU3)| exact (wmono_trans asegs _ _ _ WM12 WM3)| exact MI3].
Qed.
End ROPUG1.
