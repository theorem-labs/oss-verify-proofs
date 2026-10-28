(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg L5Defs L5Core HeapIface. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmFloatXSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Mem Exec Frame Cells Step.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer BrMem.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Spec Require Import Prelim SoftFloat FmtFp FmtFpDig.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_pad_u5 F_fmt_fp_lib_u5 F_fmt_fp_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.F6 Require Import FmtFpNF. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fmt_fp_nf_u5 FmtFpFactsC_u5 F_vsnprintf_u5 F_snprintf_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FloatX Require Import CjCpsX_u5.
Import ListNotations.
Import PML.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma zbl : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.

Section SnCps.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis NUMF : forall d prec o l, (prec = 15 \/ prec = 17) -> dfin d -> fmt_fp [] (f128_of_d d) 1 prec 0 CHR_g = Some (o, l) -> num_final o.

Theorem snprintf_g_proof : PMFX.snprintf_g_spec L.
Proof.
  unfold PMFX.snprintf_g_spec, cps_pure. intros buf p v sp r fx R M model K Hh Hl HK FPOK PRE CONT.
  destruct PRE as ((RA & RAOK & SPr & TPr & STK) & A0 & A1 & A2 & A3 & Hp & A4 & Hv & IMG & DEF & SPB & BTOP).
  destruct (fmt_fp'_g_total v p Hp) as (o & l & FM & El & Lo & FACTS & FINE & NFE).
  destruct STK as (SPA & SPL & SPH & STOP & SDEF).
  unfold PMFX.SNPRINTF_SCR in *.
  assert (Ev : bv_unsigned (getr R 14) = v) by (rewrite A4; apply unsigned_lit; lia).
  assert (Esp : bv_unsigned (getr R 2) = sp) by (rewrite SPr; apply unsigned_lit; lia).
  assert (IMG2 : L5.img_clear M 0x10000 0xc4000) by (intros i Hi; apply IMG; unfold IMG_RO_HI; lia).
  unfold cfg. eapply cj_evt_srz; [exact Hh | exact Hl | | ].
  - (* [comment removed for export] *)
    unfold canon_regs. unfold PMFX.PC_SNPRINTF.
    eapply evt_mono.
    { eapply (snprintf_star_proof (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9)
               (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19)
               (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29)
               (getr R 30) (getr R 31) fp_regs fp_csr M buf (ovl_bytes M buf 100) p (sp - 6144) (le_bytes_to_word (guard_bytes M)) o l);
        rewrite ?Ev, ?Esp.
      - exact A0.
      - exact A1.
      - unfold A_FMT_STAR. exact A2.
      - exact Hp.
      - exact A3.
      - exact FM.
      - exact FACTS.
      - exact El.
      - lia.
      - apply defined_rw_cells; [exact DEF | lia | lia].
      - apply stk_of_defined; [replace (sp - (sp - 6144)) with 6144 by lia; exact SDEF | lia | lia].
      - unfold SNPRINTF_DEPTH; lia.
      - unfold F_printf_iface_u5.GLOBALS_TOP; lia.
      - lia.
      - apply ssp_cells_c. unfold img_ro, IMG_RO_HI in IMG. exact IMG.
      - apply mem_inv_of_clear. exact IMG2.
      - exact FPOK.
      - right; lia.
      - right; unfold F_printf_iface_u5.GLOBALS_TOP; lia. }
    intros ms' P. exact P.
  - intros ms1 ms1' POST EQV.
    unfold snprintf_post, vsnprintf_post in POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' & E1 & MU & WM & MI' & FRM' & FOK & ST' & SSP' & DST').
    subst ms1.
    destruct (ms_eqv_MS_inv _ _ _ _ _ _ _ EQV) as [Ems REQ].
    rewrite Ems. set (R' := ms_regs ms1') in *.
    replace (ret_pc (getr R 1)) with (Z_to_bv 64 r) by (rewrite RA; symmetry; apply ret_pc_even; unfold L5.ra_ok in RAOK; lia).
    change (MS R' Ft (Z_to_bv 64 r) fc' None m' (seg_rom F_memset_u5.rsegs)) with (@mkst (mkFP Ft fc') R' (Z_to_bv 64 r) m' (seg_rom RSEGS)).
    rewrite Esp in MU.
    pose proof DST' as ((_ & BA) & WR). cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
    apply (CONT (mkFP Ft fc') R' m').
    + exact FRM'.
    + exists o. split.
      { destruct (dfin_dec v) as [Hfin|Hnf]; [left; exact (NUMF v p o l Hp Hfin (FINE Hfin)) | right; exact (NFE Hnf)]. }
      split; [unfold zlength in Lo; lia|].
      split. { unfold a0. rewrite <- (getr_eqv _ _ _ REQ). unfold getr; cbn. rewrite El. reflexivity. }
      split. { eapply bytes_at_L5. exact BA. }
      split. { unfold u8, L5.u8_at. destruct BA as (_ & _ & HB).
               assert (Hi : (length o < length (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) (ovl_bytes M buf 100)))%nat)
                 by (rewrite length_app, zbl; cbn [length]; lia).
               pose proof (HB (length o) Hi) as E. rewrite nth_error_app2 in E by (rewrite zbl; lia).
               rewrite zbl, Nat.sub_diag in E. cbn [nth_error] in E.
               rewrite rdn_unfold. change (Z_to_bv 64 (buf + Z.of_nat (length o))) with (wa (buf + Z.of_nat (length o))).
               lazymatch goal with |- context [mrd ?sg m' ?x] => change (mrd sg m' x) with (mrd F_memset_u5.rsegs m' x) end.
               rewrite E. rewrite rdn_unfold. reflexivity. }
      { intros i Hi. destruct WR as (_ & _ & HW). specialize (HW i ltac:(cbn; lia)).
        rewrite wview_off_image in HW by (rewrite unsigned_lit; lia). exact HW. }
    + intros rr Hrr. rewrite <- (getr_eqv _ _ rr REQ).
      unfold callee_saved_idx in Hrr.
      assert (Er : exists k, In k callee_saved_idx /\ rr = Z_to_bv 5 k).
      { exists (bv_unsigned rr). split; [exact Hrr| symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range]. }
      destruct Er as (k & Hk & ->). unfold callee_saved_idx in Hk. cbn [In] in Hk.
      repeat (destruct Hk as [<-|Hk]; [unfold getr; cbn; reflexivity|]). destruct Hk.
    + replace [(sp - 6144, 6144); (buf, 100)] with [(sp - 6144, sp - (sp - 6144)); (buf, buf + Z.of_nat 100 - buf)] by (f_equal; [f_equal; lia | f_equal; f_equal; lia]).
      apply munch2_frame_but. exact MU.
    + intros x Hx. unfold munch in MU.
      destruct (Z_le_gt_dec (sp - 6144) (bv_unsigned x)) as [X1|X1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) sp) as [X2|X2]|].
      * assert (W1 : wview CSEGS M x <> None) by (rewrite wview_off_image by lia; exact Hx).
        pose proof (WM x W1) as W2. rewrite wview_off_image in W2 by lia. exact W2.
      * destruct (Z_le_gt_dec buf (bv_unsigned x)) as [Y1|Y1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (buf + Z.of_nat 100)) as [Y2|Y2]|].
        -- assert (W1 : wview CSEGS M x <> None) by (rewrite wview_off_image by lia; exact Hx).
           pose proof (WM x W1) as W2. rewrite wview_off_image in W2 by lia. exact W2.
        -- rewrite MU; [exact Hx|]. cbn [outside]. repeat split; lia.
        -- rewrite MU; [exact Hx|]. cbn [outside]. repeat split; lia.
      * destruct (Z_le_gt_dec buf (bv_unsigned x)) as [Y1|Y1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (buf + Z.of_nat 100)) as [Y2|Y2]|].
        -- assert (W1 : wview CSEGS M x <> None) by (rewrite wview_off_image by lia; exact Hx).
           pose proof (WM x W1) as W2. rewrite wview_off_image in W2 by lia. exact W2.
        -- rewrite MU; [exact Hx|]. cbn [outside]. repeat split; lia.
        -- rewrite MU; [exact Hx|]. cbn [outside]. repeat split; lia.
Qed.
End SnCps.
